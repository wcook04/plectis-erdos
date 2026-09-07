import Erdos257PeriodNoncollapse.CarrySurvivorExtinction
import Erdos257PeriodNoncollapse.CurvatureCarry
import Erdos257PeriodNoncollapse.TotientCarryKernelRigidity

/-!
# Rational totient tails as periodic carry quotients

The finite-rank route for Erdős #249 stops at a genuine boundary: rationality
of one binary value does not make its coefficient generating function
rational, so it does not bound the rational rank of the carry's dyadic
sections.  This file records the exact positive statement that rationality
*does* supply on those sections.

For the canonical tempered carry `u = v R`, an integral tail difference

`R_(N+k) - R_N ∈ ℤ`

is equivalent to divisibility of the carry displacement

`v ∣ u_(N+k) - u_N`.

Consequently the eventual tail period makes every dyadic carry section
eventually periodic modulo the same multiplier `v`, uniformly in its level.
The same carry nevertheless has rank at least `2^e-1` through level `e`.
This is the precise quotient-compression/torsion-free-rank separation that a
future totient-specific contradiction must cross.
-/

namespace Erdos257PeriodNoncollapse

open TotientTailPeriodKiller

/-- The generic coefficient tail specializes definitionally to the local
totient tail used by the period-killer modules. -/
theorem binaryCoeffTail_totient_eq (N : ℕ) :
    binaryCoeffTail Nat.totient N = totientTail N := by
  unfold binaryCoeffTail totientTail
  apply tsum_congr
  intro j
  rw [show N + j + 1 = N + 1 + j by omega]

/-- The shifted-index generic series is the original totient series; the
missing zeroth term is `φ(0)=0`. -/
theorem binaryCoeffSeries_totient_eq :
    binaryCoeffSeries Nat.totient =
      ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  rw [summable_totient_div_two_pow.tsum_eq_zero_add]
  simp only [Nat.totient_zero, Nat.cast_zero, pow_zero, zero_div, zero_add]
  unfold binaryCoeffSeries
  apply tsum_congr
  intro n
  rfl

/-- A tempered totient carry is exactly its positive multiplier times the
local totient tail. -/
theorem totient_temperedOrbit_eq_scaledTail
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N : ℕ) :
    (u N : ℝ) = (v : ℝ) * totientTail N := by
  rw [← binaryCoeffTail_totient_eq]
  exact temperedBinaryOrbit_eq_scaledTail Nat.totient Nat.totient_le hu N

/-- Exact displacement form of tail-orbit rigidity. -/
theorem totient_carryShift_cast
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    ((u (N + k) - u N : ℤ) : ℝ) =
      (v : ℝ) * (totientTail (N + k) - totientTail N) := by
  push_cast
  rw [totient_temperedOrbit_eq_scaledTail hu (N + k),
    totient_temperedOrbit_eq_scaledTail hu N]
  ring

/-- For a positive-multiplier tempered totient carry, integrality of a tail
difference is exactly divisibility of the corresponding carry displacement.
This is the carry-side form of the tail-period law. -/
theorem carryShift_dvd_iff_tailDiff_mem_int
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N ↔
      totientTail (N + k) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hcast := totient_carryShift_cast hu N k
    have hvR : (v : ℝ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hvR)
    calc
      (v : ℝ) * (z : ℝ) = ((u (N + k) - u N : ℤ) : ℝ) := by
        exact_mod_cast hz.symm
      _ = (v : ℝ) * (totientTail (N + k) - totientTail N) := hcast
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply Int.cast_injective (α := ℝ)
    calc
      ((u (N + k) - u N : ℤ) : ℝ) =
          (v : ℝ) * (totientTail (N + k) - totientTail N) :=
        totient_carryShift_cast hu N k
      _ = (v : ℝ) * (z : ℝ) := by rw [← hz]
      _ = (((v : ℤ) * z : ℤ) : ℝ) := by norm_num

/-- Exact normalization of a divisible carry displacement.  Dividing by the
orbit multiplier does not create a compressed carry state: it recovers the
integer tail difference itself. -/
theorem carryShift_ediv_cast_eq_tailDiff
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ)
    (hdvd : (v : ℤ) ∣ u (N + k) - u N) :
    (((u (N + k) - u N) / (v : ℤ) : ℤ) : ℝ) =
      totientTail (N + k) - totientTail N := by
  obtain ⟨z, hz⟩ := hdvd
  have hvZ : (v : ℤ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [hz, Int.mul_ediv_cancel_left z hvZ]
  have hcast := totient_carryShift_cast hu N k
  have hvR : (v : ℝ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hvR)
  calc
    (v : ℝ) * (z : ℝ) = ((u (N + k) - u N : ℤ) : ℝ) := by
      exact_mod_cast hz.symm
    _ = (v : ℝ) * (totientTail (N + k) - totientTail N) := hcast

/-- Reduction modulo any divisor of the orbit multiplier erases the totient
forcing term.  Thus a finite-field reduction at a prime dividing `v` sees
only the homogeneous doubling recurrence, not the totient grid minor. -/
theorem totient_forcing_vanishes_mod_of_dvd_multiplier
    {p v : ℕ} {u : ℕ → ℤ} (hpv : p ∣ v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N : ℕ) :
    u (N + 1) ≡ 2 * u N [ZMOD (p : ℤ)] := by
  have hnat : p ∣ v * Nat.totient (N + 1) :=
    dvd_mul_of_dvd_left hpv _
  have hint : (p : ℤ) ∣ ((v * Nat.totient (N + 1) : ℕ) : ℤ) := by
    exact_mod_cast hnat
  rw [← totient_temperedOrbit_derivative hu (by omega : 0 < N + 1)] at hint
  rw [Int.modEq_iff_dvd]
  simpa [carryDerivative] using hint

/-- The preceding loss is global: modulo a divisor of `v`, the whole carry is
the geometric orbit generated by its initial state. -/
theorem totient_carry_modEq_geometric_of_dvd_multiplier
    {p v : ℕ} {u : ℕ → ℤ} (hpv : p ∣ v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) :
    ∀ N : ℕ, u N ≡ (2 : ℤ) ^ N * u 0 [ZMOD (p : ℤ)] := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep :=
        totient_forcing_vanishes_mod_of_dvd_multiplier hpv hu N
      have hscaled := ih.mul_left 2
      exact hstep.trans (by
        convert hscaled using 1 <;> simp [pow_succ] <;> ring)

/-- Divisibility of one eventual carry period propagates to every multiple of
that period by telescoping. -/
theorem carryShift_mul_dvd
    {v h N₀ : ℕ} {u : ℕ → ℤ}
    (hint : ∀ N, N₀ ≤ N → (v : ℤ) ∣ u (N + h) - u N)
    (m N : ℕ) (hN : N₀ ≤ N) :
    (v : ℤ) ∣ u (N + m * h) - u N := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := hint (N + m * h) (hN.trans (Nat.le_add_right _ _))
      rw [show N + (m + 1) * h = N + m * h + h by
        rw [Nat.succ_mul]
        omega]
      convert hstep.add ih using 1 <;> ring

/-- Uniform quotient-periodicity of all dyadic carry sections.  The period is
measured in the section variable; its ambient-index shift is `2^j h`. -/
def CarrySectionsEventuallyPeriodicMod
    (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j r n : ℕ, N₀ ≤ n →
    u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)]

/-- An eventual period of the base carry displacement gives the same
eventual period modulo `v` on every dyadic section, with one common threshold
for all levels and residues. -/
theorem carrySectionsEventuallyPeriodicMod_of_shift_dvd
    {v h N₀ : ℕ} {u : ℕ → ℤ}
    (hint : ∀ N, N₀ ≤ N → (v : ℤ) ∣ u (N + h) - u N) :
    CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  intro j r n hn
  have hbase : N₀ ≤ 2 ^ j * n + r := by
    have hnle : n ≤ 2 ^ j * n := by
      calc
        n = 1 * n := by simp
        _ ≤ 2 ^ j * n :=
          Nat.mul_le_mul_right n (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ)))
    omega
  have hdvd := carryShift_mul_dvd hint (2 ^ j) (2 ^ j * n + r) hbase
  apply Int.modEq_iff_dvd.mpr
  rw [show 2 ^ j * (n + h) + r =
      (2 ^ j * n + r) + 2 ^ j * h by ring]
  exact hdvd

/-- Rationality supplies one positive-multiplier tempered carry whose dyadic
sections are uniformly eventually periodic modulo the multiplier. -/
theorem not_irrational_totientSeries_implies_eventual_mod_period
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  obtain ⟨v, hv, u, hu⟩ :=
    (not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
      Nat.totient Nat.totient_le).mp hirr
  have hrat :
      ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
    rw [← binaryCoeffSeries_totient_eq]
    exact hirr
  obtain ⟨h, hh, N₀, hperiod⟩ := eventual_period_of_not_irrational hrat
  have hdiv : ∀ N, N₀ ≤ N → (v : ℤ) ∣ u (N + h) - u N := by
    intro N hN
    exact (carryShift_dvd_iff_tailDiff_mem_int hv hu N h).2 (hperiod N hN)
  exact ⟨v, hv, u, hu, h, hh, N₀,
    carrySectionsEventuallyPeriodicMod_of_shift_dvd hdiv⟩

/-- **Exact rationality frontier.**  The same rationality-supplied carry has
uniform eventual periodicity modulo `v` and unbounded torsion-free dyadic
section rank.  Hence quotient periodicity is the valid compression theorem;
it cannot be promoted to finite `ℚ`-rank without extra totient arithmetic. -/
theorem not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  obtain ⟨v, hv, u, hu⟩ :=
    (not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
      Nat.totient Nat.totient_le).mp hirr
  have hrat :
      ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
    rw [← binaryCoeffSeries_totient_eq]
    exact hirr
  obtain ⟨h, hh, N₀, hperiod⟩ := eventual_period_of_not_irrational hrat
  have hdiv : ∀ N, N₀ ≤ N → (v : ℤ) ∣ u (N + h) - u N := by
    intro N hN
    exact (carryShift_dvd_iff_tailDiff_mem_int hv hu N h).2 (hperiod N hN)
  refine ⟨v, hv, u, hu, ?_, h, hh, N₀,
    carrySectionsEventuallyPeriodicMod_of_shift_dvd hdiv⟩
  intro e
  exact finrank_canonicalCarryKernel_ge_of_linearIndependent hv hu e
    (linearIndependent_canonicalTotientKernelFamily e)

/-! ## Absolute-adjugate tail bounds cannot close -/

/-- The crude two-tail cost attached to an inverse/adjugate row.  Recovering
`φ(x)` as `2 R_(x-1) - R_x` and applying `R_M ≤ M+2` termwise gives
the factor `2(x+1) + (x+2)`. -/
noncomputable def totientAdjugateTailCost
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ) : ℚ :=
  ∑ i, |w i| * (2 * ((x i : ℚ) + 1) + ((x i : ℚ) + 2))

/-- **Universal absolute-adjugate no-go.**  Any rational row that exactly
isolates one totient channel already has crude two-tail cost at least `3`.
Indeed `φ(x) ≤ x` forces `1 ≤ Σ |w_i| x_i`, while reconstructing each
coefficient from two tails costs `3 x_i + 4`.  This is independent of the
matrix height, row translation, determinant, and choice of target channel. -/
theorem three_le_totientAdjugateTailCost
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (Nat.totient (x i) : ℚ) = 1) :
    (3 : ℚ) ≤ totientAdjugateTailCost w x := by
  classical
  have habs :
      (1 : ℚ) ≤ ∑ i, |w i| * (Nat.totient (x i) : ℚ) := by
    calc
      (1 : ℚ) = |∑ i, w i * (Nat.totient (x i) : ℚ)| := by
        rw [hisolate, abs_one]
      _ ≤ ∑ i, |w i * (Nat.totient (x i) : ℚ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |w i| * (Nat.totient (x i) : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        have hphiNonneg : (0 : ℚ) ≤ (Nat.totient (x i) : ℚ) := by
          exact_mod_cast Nat.zero_le (Nat.totient (x i))
        rw [abs_mul, abs_of_nonneg hphiNonneg]
  have hphi :
      (∑ i, |w i| * (Nat.totient (x i) : ℚ)) ≤
        ∑ i, |w i| * (x i : ℚ) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast Nat.totient_le (x i)
    · exact abs_nonneg (w i)
  have hmass : (1 : ℚ) ≤ ∑ i, |w i| * (x i : ℚ) :=
    habs.trans hphi
  calc
    (3 : ℚ) = 3 * 1 := by ring
    _ ≤ 3 * ∑ i, |w i| * (x i : ℚ) := by nlinarith
    _ = ∑ i, 3 * (|w i| * (x i : ℚ)) := by rw [Finset.mul_sum]
    _ ≤ totientAdjugateTailCost w x := by
      unfold totientAdjugateTailCost
      apply Finset.sum_le_sum
      intro i _
      have hwi : (0 : ℚ) ≤ |w i| := abs_nonneg _
      nlinarith

/-- Therefore the absolute-adjugate strategy can never reach its required
strict `< 1` tail-error threshold, at any finite grid height. -/
theorem not_totientAdjugateTailCost_lt_one
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (Nat.totient (x i) : ℚ) = 1) :
    ¬ totientAdjugateTailCost w x < 1 := by
  intro hlt
  have hthree := three_le_totientAdjugateTailCost w x hisolate
  linarith

/-! ## Primitive Mersenne primes alone do not kill a tail period -/

/-- The completely multiplicative control sequence `c(n)=n` has the exact
tail `T_c(N)=N+2`.  In particular its marked binary value is rational, while
every positive shift has an integral tail difference. -/
theorem idCoeff_binaryCoeffTail_eq (N : ℕ) :
    binaryCoeffTail id N = (N : ℝ) + 2 := by
  have h := temperedBinaryOrbit_eq_scaledTail id (fun n ↦ le_rfl)
    idCoeff_temperedOrbit N
  norm_num at h ⊢
  exact h.symm

/-- Exact shift law for the multiplicative rational control. -/
theorem idCoeff_binaryCoeffTail_sub (N K : ℕ) :
    binaryCoeffTail id (N + K) - binaryCoeffTail id N = (K : ℝ) := by
  rw [idCoeff_binaryCoeffTail_eq, idCoeff_binaryCoeffTail_eq]
  push_cast
  ring

/-- **Primitive-Mersenne congruence no-go.**  Suppose `q` is any modulus
strictly above `K` which divides `2^K-1`; this includes the size conclusion
supplied by a primitive prime divisor.  The rational, completely
multiplicative control `c(n)=n` has an integral `K`-shift at every `N`, but
that integer is `K` and hence is nonzero modulo `q`.  Thus a primitive factor
of the homogeneous multiplier `2^K-1` supplies no contradiction from tail
integrality alone.  A successful use of such a factor must add a genuinely
totient-specific residue/size restriction. -/
theorem idCoeff_mersenneModulus_does_not_annihilate_tailShift
    {K q : ℕ} (hK : 0 < K) (hKq : K < q) (hqM : q ∣ 2 ^ K - 1) :
    binaryCoeffSeries id = 2 ∧ q ∣ 2 ^ K - 1 ∧
      ∀ N : ℕ, ∃ z : ℤ,
        (z : ℝ) = binaryCoeffTail id (N + K) - binaryCoeffTail id N ∧
          ¬ (q : ℤ) ∣ z := by
  refine ⟨?_, hqM, ?_⟩
  · simpa using idCoeff_binaryCoeffTail_eq 0
  · intro N
    refine ⟨(K : ℤ), ?_, ?_⟩
    · rw [idCoeff_binaryCoeffTail_sub]
      norm_num
    · intro hdvd
      have hnat : q ∣ K := by exact_mod_cast hdvd
      have hqle : q ≤ K := Nat.le_of_dvd hK hnat
      omega

/-! ## A cofinal totient-specific mod-four pulse -/

/-- A prime divisor congruent to one modulo four forces four to divide the
totient. -/
theorem four_dvd_totient_of_prime_modEq_one_dvd
    {r n : ℕ} (hr : r.Prime) (hr4 : r ≡ 1 [MOD 4]) (hrn : r ∣ n) :
    4 ∣ Nat.totient n := by
  have h4pred : 4 ∣ r - 1 :=
    (Nat.modEq_iff_dvd' hr.one_le).mp hr4.symm
  have htot : Nat.totient r ∣ Nat.totient n :=
    Nat.totient_dvd_of_dvd hrn
  rw [Nat.totient_prime hr] at htot
  exact h4pred.trans htot

/-- Every positive shift divisible by four has cofinally many prime inputs
where its totient increment is exactly `2 mod 4`.

Choose a fresh prime `r = 1 mod 4` above the shift and use Dirichlet on the
coprime progression

`p = (3r - H) mod 4r`,  where `H = 4h`.

Then `p = 3 mod 4`, so `φ(p) = 2 mod 4`, while `r ∣ p+H` forces
`4 ∣ φ(p+H)`.  Unlike a homogeneous Mersenne factor, this is a
genuinely totient-specific residue and is supplied beyond every threshold. -/
theorem exists_prime_deltaTotient_four_mul_mod_four_two
    (h B : ℕ) (hh : 0 < h) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      deltaTotient (4 * h) p ≡ (2 : ℤ) [ZMOD 4] := by
  let H := 4 * h
  have hHpos : 0 < H := by dsimp [H]; omega
  obtain ⟨q, _hqinj, hq⟩ :=
    exists_large_distinct_primes_modEq_one (ι := Fin 1) 2 H
  let i : Fin 1 := ⟨0, by omega⟩
  let r := q i
  have hr : r.Prime := by simpa [r] using (hq i).1
  have hr4 : r ≡ 1 [MOD 4] := by
    simpa [r] using (hq i).2.1
  have hHr : H < r := by simpa [r] using (hq i).2.2
  have hrne2 : r ≠ 2 := by omega
  have hrodd : Odd r := Nat.odd_iff.mpr
    (hr.eq_two_or_odd.resolve_left hrne2)
  let base := 3 * r - H
  let step := 4 * r
  have hH3r : H ≤ 3 * r := by omega
  have hHeven : Even H := by
    refine ⟨2 * h, ?_⟩
    dsimp [H]
    ring
  have hbaseOdd : Odd base := by
    apply Nat.Odd.sub_even hH3r
    · have hthree : Odd (3 : ℕ) := ⟨1, by omega⟩
      exact hthree.mul hrodd
    · exact hHeven
  have hbaseCoprimeFour : base.Coprime 4 := by
    simpa using hbaseOdd.coprime_two_right.pow_right 2
  have hHCoprimeR : H.Coprime r := by
    have hnrd : ¬ r ∣ H := Nat.not_dvd_of_pos_of_lt hHpos hHr
    exact (hr.coprime_iff_not_dvd.mpr hnrd).symm
  have hbaseEq : base = (r - H) + 2 * r := by
    dsimp [base]
    omega
  have hbaseCoprimeR : base.Coprime r := by
    rw [hbaseEq, Nat.coprime_add_mul_right_left,
      Nat.coprime_self_sub_left hHr.le]
    exact hHCoprimeR
  have hbaseCoprimeStep : base.Coprime step := by
    dsimp [step]
    exact hbaseCoprimeFour.mul_right hbaseCoprimeR
  obtain ⟨p, hpBound, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B base)
      (q := step) (a := base) (by dsimp [step]; omega)
      hbaseCoprimeStep
  have hbasep : base ≤ p :=
    (Nat.le_max_right B base).trans hpBound.le
  have hstepdvd : step ∣ p - base :=
    (Nat.modEq_iff_dvd' hbasep).mp hpmod.symm
  obtain ⟨t, ht⟩ := hstepdvd
  have hpEq : p = base + step * t := by omega
  have h3rmod : 3 * r ≡ 3 [MOD 4] := by
    simpa using hr4.mul_left 3
  have hHmod : H ≡ 0 [MOD 4] := by
    apply Nat.modEq_zero_iff_dvd.mpr
    refine ⟨h, ?_⟩
    dsimp [H]
  have hbaseMod : base ≡ 3 [MOD 4] := by
    have hsub := h3rmod.sub hH3r (by omega : 0 ≤ (3 : ℕ)) hHmod
    simpa [base] using hsub
  have hfourStep : 4 ∣ step := by
    refine ⟨r, ?_⟩
    simp [step]
  have hp3 : p ≡ 3 [MOD 4] :=
    (hpmod.of_dvd hfourStep).trans hbaseMod
  have hbaseAdd : base + H = 3 * r := by
    dsimp [base]
    exact Nat.sub_add_cancel hH3r
  have hrTop : r ∣ p + H := by
    refine ⟨3 + 4 * t, ?_⟩
    calc
      p + H = (base + step * t) + H := by rw [hpEq]
      _ = (base + H) + step * t := by ring
      _ = 3 * r + (4 * r) * t := by rw [hbaseAdd]
      _ = r * (3 + 4 * t) := by ring
  have hfourTop : 4 ∣ Nat.totient (p + H) :=
    four_dvd_totient_of_prime_modEq_one_dvd hr hr4 hrTop
  have hp3le : 3 ≤ p := by
    have hbasePos : 0 < base := by dsimp [base]; omega
    omega
  have hfourPred : 4 ∣ p - 3 :=
    (Nat.modEq_iff_dvd' hp3le).mp hp3.symm
  obtain ⟨A, hA⟩ := hfourTop
  obtain ⟨b, hb⟩ := hfourPred
  have hpForm : p = 4 * b + 3 := by omega
  refine ⟨p, (Nat.le_max_left B base).trans_lt hpBound, hp, ?_⟩
  rw [Int.modEq_iff_dvd]
  refine ⟨(b : ℤ) + 1 - (A : ℤ), ?_⟩
  unfold deltaTotient
  rw [show 4 * h = H by rfl, hA, Nat.totient_prime hp, hpForm]
  push_cast
  ring

/-- Once both arguments exceed two, a totient increment is even. -/
theorem deltaTotient_even_of_three_le (H n : ℕ) (hn : 3 ≤ n) :
    Even (deltaTotient H n) := by
  have htop : 2 < n + H := by omega
  have hbot : 2 < n := by omega
  obtain ⟨u, hu⟩ := Nat.totient_even htop
  obtain ⟨v, hv⟩ := Nat.totient_even hbot
  refine ⟨(u : ℤ) - (v : ℤ), ?_⟩
  unfold deltaTotient
  rw [hu, hv]
  push_cast
  ring

/-- A fixed arithmetic pulse transfers to the integral tail orbit.  This is
the pointwise form used below: eventual integrality is only needed two steps
before `p`, while the conclusion is the `2 mod 4` state at `p`. -/
theorem integral_four_mul_tailDiff_mod_four_two_of_delta_pulse
    {h N₀ p : ℕ} (hpLarge : N₀ + 3 < p)
    (hpulse : deltaTotient (4 * h) p ≡ (2 : ℤ) [ZMOD 4])
    (hint : ∀ N, N₀ ≤ N →
      totientTail (N + 4 * h) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ)) :
    ∃ z : ℤ,
      (z : ℝ) = totientTail (p + 4 * h) - totientTail p ∧
        z ≡ (2 : ℤ) [ZMOD 4] := by
  obtain ⟨d₀, hd₀⟩ := hint (p - 2) (by omega)
  let d₁ : ℤ := 2 * d₀ - deltaTotient (4 * h) (p - 1)
  have hd₁ : (d₁ : ℝ) =
      totientTail (p - 1 + 4 * h) - totientTail (p - 1) := by
    dsimp [d₁]
    push_cast
    rw [hd₀]
    simpa [show p - 2 + 1 = p - 1 by omega] using
      (tail_diff_succ (4 * h) (p - 2)).symm
  have hdeltaEven : Even (deltaTotient (4 * h) (p - 1)) :=
    deltaTotient_even_of_three_le (4 * h) (p - 1) (by omega)
  have hd₁Even : Even d₁ := by
    dsimp [d₁]
    exact (even_two_mul d₀).sub hdeltaEven
  let d₂ : ℤ := 2 * d₁ - deltaTotient (4 * h) p
  have hd₂ : (d₂ : ℝ) =
      totientTail (p + 4 * h) - totientTail p := by
    dsimp [d₂]
    push_cast
    rw [hd₁]
    simpa [show p - 1 + 1 = p by omega] using
      (tail_diff_succ (4 * h) (p - 1)).symm
  have htwod₁ : 2 * d₁ ≡ (0 : ℤ) [ZMOD 4] := by
    apply Int.modEq_zero_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hd₁Even
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  have hd₂mod : d₂ ≡ (2 : ℤ) [ZMOD 4] := by
    have hsub := htwod₁.sub hpulse
    have hd₂neg : d₂ ≡ (-2 : ℤ) [ZMOD 4] := by
      simpa [d₂] using hsub
    have hneg : (-2 : ℤ) ≡ (2 : ℤ) [ZMOD 4] := by
      apply Int.modEq_iff_dvd.mpr
      norm_num
    exact hd₂neg.trans hneg
  exact ⟨d₂, hd₂, hd₂mod⟩

/-- **Cofinal mod-four tail-orbit pulse.**  If the `4h` tail difference is
eventually integral, the preceding arithmetic producer forces cofinally many
prime positions where its integer representative is `2 mod 4`.

The first recurrence step makes the predecessor representative even because
both totients are even.  At the prime pulse, twice that predecessor vanishes
modulo four and the `2 mod 4` increment leaves another `2 mod 4` state.  This
is a new rationality-side constraint on the actual totient orbit; the
completely multiplicative control `c(n)=n` has shift `4h = 0 mod 4` and
cannot realize it. -/
theorem eventual_integral_four_mul_tailDiff_has_cofinal_mod_four_pulse
    {h N₀ : ℕ} (hh : 0 < h)
    (hint : ∀ N, N₀ ≤ N →
      totientTail (N + 4 * h) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ)) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + 4 * h) - totientTail p ∧
        z ≡ (2 : ℤ) [ZMOD 4] := by
  intro B
  obtain ⟨p, hpBound, hp, hpulse⟩ :=
    exists_prime_deltaTotient_four_mul_mod_four_two h (max B (N₀ + 3)) hh
  have hpLarge : N₀ + 3 < p :=
    (Nat.le_max_right B (N₀ + 3)).trans_lt hpBound
  obtain ⟨d₂, hd₂, hd₂mod⟩ :=
    integral_four_mul_tailDiff_mod_four_two_of_delta_pulse
      hpLarge hpulse hint
  exact ⟨p, (Nat.le_max_left B (N₀ + 3)).trans_lt hpBound,
    hp, d₂, hd₂, hd₂mod⟩

/-! ## Fixed-depth residue reset: the exact congruence boundary -/

/-- Two carry orbits driven by the same totient increments differ only by
the homogeneous multiplier `2^L`.  In particular, changing the integral
tail state at the left endpoint cannot change the right endpoint modulo
`2^L`. -/
theorem carryOrbit_sub (h N : ℕ) (d e : ℤ) :
    ∀ L : ℕ,
      carryOrbit h N d L - carryOrbit h N e L =
        (2 : ℤ) ^ L * (d - e) := by
  intro L
  induction L with
  | zero => simp [carryOrbit]
  | succ L ih =>
      simp only [carryOrbit, pow_succ]
      calc
        (2 * carryOrbit h N d L - deltaTotient h (N + L + 1)) -
              (2 * carryOrbit h N e L - deltaTotient h (N + L + 1)) =
            2 * (carryOrbit h N d L - carryOrbit h N e L) := by ring
        _ = 2 * ((2 : ℤ) ^ L * (d - e)) := by rw [ih]
        _ = (2 : ℤ) ^ L * 2 * (d - e) := by ring

/-- The orbit launched from zero is exactly the negative signed prefix
word.  Thus `windowDiscrepancy` is not an additional state coordinate: it is
the forcing response of the same affine carry recurrence. -/
theorem carryOrbit_zero_eq_neg_windowDiscrepancy (h N L : ℕ) :
    carryOrbit h N 0 L = -windowDiscrepancy h N L := by
  induction L with
  | zero => simp [carryOrbit, windowDiscrepancy]
  | succ L ih =>
      simp only [carryOrbit]
      rw [windowDiscrepancy_succ, ih]
      ring

/-- **Closed form for every integral carry trajectory.**  After `L` steps,
the initial state contributes only `2^L d`; all lower binary digits are the
negative discrepancy word. -/
theorem carryOrbit_eq_twoPow_mul_sub_windowDiscrepancy
    (h N : ℕ) (d : ℤ) (L : ℕ) :
    carryOrbit h N d L =
      (2 : ℤ) ^ L * d - windowDiscrepancy h N L := by
  calc
    carryOrbit h N d L =
        (carryOrbit h N d L - carryOrbit h N 0 L) +
          carryOrbit h N 0 L := by ring
    _ = (2 : ℤ) ^ L * (d - 0) +
          (-windowDiscrepancy h N L) := by
      rw [carryOrbit_sub, carryOrbit_zero_eq_neg_windowDiscrepancy]
    _ = (2 : ℤ) ^ L * d - windowDiscrepancy h N L := by ring

/-- Fixed-depth reset in its pure integer-orbit form. -/
theorem carryOrbit_modEq_neg_windowDiscrepancy
    (h N : ℕ) (d : ℤ) (L : ℕ) :
    carryOrbit h N d L ≡
      -windowDiscrepancy h N L [ZMOD (2 : ℤ) ^ L] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-d, ?_⟩
  rw [carryOrbit_eq_twoPow_mul_sub_windowDiscrepancy]
  ring

/-- **Exact fixed-depth reset for an integral totient tail difference.**
Once the left endpoint is integral, the right endpoint is integral and its
residue modulo `2^L` is forced by the last `L` totient increments alone:

`D_h(N+L) = -windowDiscrepancy(h,N,L)  (mod 2^L)`.

Consequently, splitting the orbit into eventual-period blocks, choosing two
Dirichlet progressions separated by a period, or telescoping the recurrence
cannot produce a second incompatible endpoint residue.  Any contradiction
using the cofinal mod-four pulse must add an independent archimedean strip or
size restriction. -/
theorem integral_tailDiff_endpoint_modEq_neg_windowDiscrepancy
    {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (L : ℕ) :
    ∃ z : ℤ,
      (z : ℝ) = totientTail (N + L + h) - totientTail (N + L) ∧
        z ≡ -windowDiscrepancy h N L [ZMOD (2 : ℤ) ^ L] := by
  refine ⟨carryOrbit h N d L, carryOrbit_eq_tail_diff hd L, ?_⟩
  exact carryOrbit_modEq_neg_windowDiscrepancy h N d L

/-- **The independent archimedean coupling.**  Negating the true integral
endpoint gives an `endpointSurvivor`: it has the discrepancy residue forced
by the reset theorem, and the analytic tail bound keeps it inside the signed
strip.  This is the exact place where congruence information and size
information meet. -/
theorem integral_tailDiff_has_endpointSurvivor
    {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (L : ℕ) :
    endpointSurvivor h N L (-carryOrbit h N d L) := by
  constructor
  · have hstripR := abs_tail_diff_lt h (N + L)
    have htrack := carryOrbit_eq_tail_diff hd L
    rw [← htrack] at hstripR
    have hstripZ :
        |carryOrbit h N d L| < ((N + L + h + 2 : ℕ) : ℤ) := by
      exact_mod_cast hstripR
    rw [abs_neg]
    push_cast at hstripZ ⊢
    omega
  · have hreset := carryOrbit_modEq_neg_windowDiscrepancy h N d L
    have hneg := hreset.neg
    simpa using hneg

/-! ## Exact infinite carry-lock classification -/

/-- An integer launch survives every carry depth inside the sharp integer
strip forced by the analytic tail bound.  The radius is one below the real
bound because the orbit is integer-valued. -/
def BoundedTailCarry (h N : ℕ) (d : ℤ) : Prop :=
  ∀ i : ℕ, |carryOrbit h N d i| ≤ (N + i + h + 1 : ℤ)

/-- An integral tail difference launches a carry that survives forever.
This is the infinite-orbit half of the edge-lock classification. -/
theorem boundedTailCarry_of_integral_tailDiff
    {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) :
    BoundedTailCarry h N d := by
  intro i
  have hstripR := abs_tail_diff_lt h (N + i)
  have htrack := carryOrbit_eq_tail_diff hd i
  rw [← htrack] at hstripR
  have hstripZ :
      |carryOrbit h N d i| < ((N + i + h + 2 : ℕ) : ℤ) := by
    exact_mod_cast hstripR
  push_cast at hstripZ ⊢
  omega

/-- Conversely, a linearly bounded integer carry cannot evade every finite
central-arc certificate unless the original tail difference is integral.
Certificate completeness supplies a killing depth for every non-integral
tail; the bounded carry supplies an endpoint survivor at that same depth. -/
theorem tail_diff_mem_int_of_boundedTailCarry
    {h N : ℕ} {d : ℤ} (hbounded : BoundedTailCarry h N d) :
    totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  by_contra hnot
  obtain ⟨L, hcert⟩ := exists_certifiedKill_of_tail_diff_notMem_int hnot
  apply no_endpointSurvivor_of_certifiedKill hcert (-carryOrbit h N d L)
  constructor
  · rw [abs_neg]
    have hbound := hbounded L
    push_cast at hbound ⊢
    omega
  · have hreset := carryOrbit_modEq_neg_windowDiscrepancy h N d L
    have hneg := hreset.neg
    simpa using hneg

/-- **Exact edge-lock classification.**  A shifted totient-tail difference is
an integer iff some integer launch of the affine carry recurrence remains
inside the linear strip at every depth.  Thus the apparent infinite lock and
the analytic integrality obstruction are the same mathematical object. -/
theorem tail_diff_mem_int_iff_exists_boundedTailCarry (h N : ℕ) :
    (totientTail (N + h) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ)) ↔
      ∃ d : ℤ, BoundedTailCarry h N d := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, boundedTailCarry_of_integral_tailDiff hd⟩
  · rintro ⟨d, hbounded⟩
    exact tail_diff_mem_int_of_boundedTailCarry hbounded

/-- No finite endpoint certificate exists exactly when an infinite bounded
carry survives.  This is the certificate-level form of the classification:
finite extinction and infinite lock are complementary, with no gap. -/
theorem no_certifiedKill_iff_exists_boundedTailCarry (h N : ℕ) :
    (∀ L : ℕ, ¬ certifiedKill h N L) ↔
      ∃ d : ℤ, BoundedTailCarry h N d := by
  constructor
  · intro hnone
    rw [← tail_diff_mem_int_iff_exists_boundedTailCarry]
    by_contra hnot
    obtain ⟨L, hcert⟩ := exists_certifiedKill_of_tail_diff_notMem_int hnot
    exact hnone L hcert
  · rintro ⟨d, hbounded⟩ L hcert
    exact tail_diff_notMem_int_of_certifiedKill hcert
      (tail_diff_mem_int_of_boundedTailCarry hbounded)

/-! ## A genuinely sharper one-sided tail strip -/

/-- Positivity of both tails gives the directed bounds that are lost when
`abs_tail_diff_lt` symmetrizes the interval. -/
theorem tail_diff_directed_bounds (h N : ℕ) :
    -((N : ℝ) + 2) < totientTail (N + h) - totientTail N ∧
      totientTail (N + h) - totientTail N < (N : ℝ) + h + 2 := by
  have htopPos := totientTail_pos (N + h)
  have hbotPos := totientTail_pos N
  have htopLe := totientTail_le (N + h)
  have hbotLe := totientTail_le N
  push_cast at htopLe
  constructor <;> linarith

/-- The asymmetric central-arc certificate.  Its low radius is only
`N+L+2`, while its high wrap radius remains `N+h+L+2`.  It is therefore
strictly weaker—and potentially strictly more useful—than `certifiedKill`
when `h>0`. -/
def directedCertifiedKill (h N L : ℕ) : Prop :=
  (N + L + 2 : ℤ) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
    windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
      (2 : ℤ) ^ L - (N + h + L + 2 : ℤ)

instance (h N L : ℕ) : Decidable (directedCertifiedKill h N L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Soundness of the directed certificate.  The proof keeps the positive
and negative endpoint radii separate instead of replacing both by their
maximum. -/
theorem tail_diff_notMem_int_of_directedCertifiedKill
    {h N L : ℕ} (hcert : directedCertifiedKill h N L) :
    totientTail (N + h) - totientTail N ∉
      Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨d, hd⟩
  obtain ⟨z, hz, hzmod⟩ :=
    integral_tailDiff_endpoint_modEq_neg_windowDiscrepancy hd L
  let y : ℤ := -z
  let P : ℤ := (2 : ℤ) ^ L
  let r : ℤ := windowDiscrepancy h N L % P
  have hymod : y % P = r := by
    have hneg := hzmod.neg
    simpa [y, P, r] using hneg
  have hbounds := tail_diff_directed_bounds h (N + L)
  rw [← hz] at hbounds
  have hzlo : -(N + L + 2 : ℤ) < z := by
    exact_mod_cast hbounds.1
  have hzhi : z < (N + L + h + 2 : ℤ) := by
    exact_mod_cast hbounds.2
  have hylo : -(N + h + L + 2 : ℤ) < y := by
    dsimp [y]
    omega
  have hyhi : y < (N + L + 2 : ℤ) := by
    dsimp [y]
    omega
  have hPpos : 0 < P := by positivity
  have hdecomp : P * (y / P) + r = y := by
    rw [← hymod]
    exact Int.mul_ediv_add_emod y P
  by_cases hq : 0 ≤ y / P
  · have hnonneg : 0 ≤ P * (y / P) := mul_nonneg hPpos.le hq
    have hrlow : (N + L + 2 : ℤ) ≤ r := by
      exact hcert.1
    linarith
  · have hqneg : y / P ≤ -1 := by omega
    have hmultiple : P * (y / P) ≤ -P := by nlinarith
    have hrhigh : r ≤ P - (N + h + L + 2 : ℤ) := by
      exact hcert.2
    linarith

/-- Every symmetric certificate is a directed certificate; the converse can
fail on the newly exposed one-sided band. -/
theorem directedCertifiedKill_of_certifiedKill
    {h N L : ℕ} (hcert : certifiedKill h N L) :
    directedCertifiedKill h N L := by
  constructor
  · have hle : (N + L + 2 : ℤ) ≤ (N + h + L + 2 : ℤ) := by omega
    exact hle.trans hcert.1.le
  · exact hcert.2.le

/-- The directed certificate is complete as well as sound: its wider finite
arc changes the first firing depth, not the underlying pointwise proposition. -/
theorem exists_directedCertifiedKill_iff_tail_diff_notMem_int
    (h N : ℕ) :
    (∃ L : ℕ, directedCertifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉
        Set.range ((↑) : ℤ → ℝ) := by
  constructor
  · rintro ⟨L, hcert⟩
    exact tail_diff_notMem_int_of_directedCertifiedKill hcert
  · intro hnon
    obtain ⟨L, hcert⟩ :=
      exists_certifiedKill_of_tail_diff_notMem_int hnon
    exact ⟨L, directedCertifiedKill_of_certifiedKill hcert⟩

/-- Concrete strictness witness on the canonical LCM diagonal: the directed
strip kills height `t=3` at depth six, one full binary level before the
symmetric certificate can fire. -/
theorem directedCertifiedKill_periodLcm_three_depth_six :
    directedCertifiedKill (periodLcm 3) (periodLcm 3) 6 := by
  decide

theorem not_certifiedKill_periodLcm_three_depth_six :
    ¬ certifiedKill (periodLcm 3) (periodLcm 3) 6 := by
  decide

/-- Multiple-period reduction using the sharper directed strip. -/
theorem irrational_totientSeries_of_multiple_directedCertificateSupply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L,
        directedCertifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h, hh, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨m, _hm, N, hN, L, hkill⟩ := hsupply h hh N₀
  exact tail_diff_notMem_int_of_directedCertifiedKill hkill
    (tail_diff_mul_mem_int hint m N hN)

/-- The canonical diagonal version of the directed certificate supply. -/
def CofinalDirectedLcmCertificateSupply : Prop :=
  ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
    directedCertifiedKill (periodLcm t) (periodLcm t) L

/-- **Exact ceiling of the directed LCM route.**  Cofinal directed
certificates are equivalent to Erdős #249 itself.  The asymmetric strip is a
real finite-depth improvement, but the current LCM diagonal does not turn it
into an independent sieve theorem: proving its cofinal supply is already
proving the original irrationality statement. -/
theorem irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      CofinalDirectedLcmCertificateSupply := by
  constructor
  · intro hirr t₀
    have hnon :=
      (irrational_totient_series_iff_all_tail_diffs_nonintegral.mp hirr)
        (periodLcm t₀) (periodLcm_pos t₀) (periodLcm t₀)
    obtain ⟨L, hcert⟩ :=
      exists_certifiedKill_of_tail_diff_notMem_int hnon
    exact ⟨t₀, le_rfl, L, directedCertifiedKill_of_certifiedKill hcert⟩
  · intro hsupply
    apply irrational_totientSeries_of_multiple_directedCertificateSupply
    intro h₀ hh N₀
    obtain ⟨t, ht, L, hcert⟩ := hsupply (max h₀ N₀)
    have hh₀t : h₀ ≤ t := (le_max_left h₀ N₀).trans ht
    have hN₀t : N₀ ≤ t := (le_max_right h₀ N₀).trans ht
    have hdvd : h₀ ∣ periodLcm t := dvd_periodLcm hh hh₀t
    have hHpos : 0 < periodLcm t := periodLcm_pos t
    have hmpos : 0 < periodLcm t / h₀ :=
      Nat.div_pos (Nat.le_of_dvd hHpos hdvd) hh
    refine ⟨periodLcm t / h₀, hmpos, periodLcm t,
      hN₀t.trans (le_periodLcm t), L, ?_⟩
    rwa [Nat.div_mul_cancel hdvd]

/-- The two extra input bits supplied by `d = 2 mod 4` lift the usual
depth-`L` endpoint test from modulus `2^L` to modulus `2^(L+2)`.  The target
residue is the half-turn `2^(L+1)` minus the discrepancy word.  This reduces
the explicit start-state search, but it is only a shifted-coordinate view of
the ordinary depth-`(L+2)` certificate once the two-letter pulse prefix is
included; no stronger cofinal supply is claimed. -/
def modFourPulseCertifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) <
      ((2 : ℤ) ^ (L + 1) - windowDiscrepancy h N L) %
        (2 : ℤ) ^ (L + 2) ∧
    ((2 : ℤ) ^ (L + 1) - windowDiscrepancy h N L) %
        (2 : ℤ) ^ (L + 2) <
      (2 : ℤ) ^ (L + 2) - (N + h + L + 2 : ℤ)

instance (h N L : ℕ) : Decidable (modFourPulseCertifiedKill h N L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Any representative of a residue in the central arc has absolute value
larger than the excluded boundary radius. -/
theorem abs_gt_of_emod_mem_central
    {x P B : ℤ} (hP : 0 < P)
    (hlow : B < x % P) (hhigh : x % P < P - B) :
    B < |x| := by
  have hr0 : 0 ≤ x % P := Int.emod_nonneg x hP.ne'
  have hrlt : x % P < P := Int.emod_lt_of_pos x hP
  have hdecomp : P * (x / P) + x % P = x :=
    Int.mul_ediv_add_emod x P
  by_cases hq : 0 ≤ x / P
  · have hPx : 0 ≤ P * (x / P) := mul_nonneg hP.le hq
    have hx0 : 0 ≤ x := by linarith
    rw [abs_of_nonneg hx0]
    linarith
  · have hqneg : x / P ≤ -1 := by omega
    have hmultiple : P * (x / P) ≤ -P := by nlinarith
    have hx0 : x ≤ 0 := by linarith
    rw [abs_of_nonpos hx0]
    linarith

/-- Exact lifted endpoint residue for a `2 mod 4` start state. -/
theorem carryOrbit_emod_twoPow_add_two_of_modFourPulse
    {h N : ℕ} {d : ℤ} (hdmod : d ≡ (2 : ℤ) [ZMOD 4]) (L : ℕ) :
    carryOrbit h N d L % (2 : ℤ) ^ (L + 2) =
      ((2 : ℤ) ^ (L + 1) - windowDiscrepancy h N L) %
        (2 : ℤ) ^ (L + 2) := by
  have hdvd : (4 : ℤ) ∣ 2 - d :=
    Int.modEq_iff_dvd.mp hdmod
  obtain ⟨q, hq⟩ := hdvd
  have hcong : carryOrbit h N d L ≡
      (2 : ℤ) ^ (L + 1) - windowDiscrepancy h N L
        [ZMOD (2 : ℤ) ^ (L + 2)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨q, ?_⟩
    rw [carryOrbit_eq_twoPow_mul_sub_windowDiscrepancy]
    rw [show (2 : ℤ) ^ (L + 2) = (2 : ℤ) ^ L * 4 by
      rw [pow_add]
      norm_num]
    rw [show (2 : ℤ) ^ (L + 1) = (2 : ℤ) ^ L * 2 by
      rw [pow_add]
      norm_num]
    calc
      (2 : ℤ) ^ L * 2 - windowDiscrepancy h N L -
            ((2 : ℤ) ^ L * d - windowDiscrepancy h N L) =
          (2 : ℤ) ^ L * (2 - d) := by ring
      _ = (2 : ℤ) ^ L * (4 * q) := by rw [hq]
      _ = (2 : ℤ) ^ L * 4 * q := by ring
  exact hcong

/-! ## The pulse-restricted survivor problem -/

/-- A finite survivor certificate restricted to the only start states that
the cofinal arithmetic pulse permits.  Compared with `survivorKill`, this
checks only candidates congruent to `2 mod 4`, a fourfold reduction of the
initial strip. -/
def modFourPulseSurvivorKill (h N K : ℕ) : Prop :=
  ∀ j ∈ Finset.range (2 * (N + h + 1) + 1),
    ((j : ℤ) - (N + h + 1) : ℤ) ≡ (2 : ℤ) [ZMOD 4] →
      ∃ i ∈ Finset.range (K + 1),
        carryOrbit h N ((j : ℤ) - (N + h + 1)) i ≤
            -(N + i + h + 2 : ℤ) ∨
          (N + i + h + 2 : ℤ) ≤
            carryOrbit h N ((j : ℤ) - (N + h + 1)) i

instance (h N K : ℕ) : Decidable (modFourPulseSurvivorKill h N K) := by
  unfold modFourPulseSurvivorKill
  infer_instance

/-- The lifted one-residue certificate eliminates every pulse-compatible
start state by depth `L`; hence it implies the finite restricted survivor
certificate without enumerating those states individually. -/
theorem modFourPulseSurvivorKill_of_certifiedKill
    {h N L : ℕ} (hcert : modFourPulseCertifiedKill h N L) :
    modFourPulseSurvivorKill h N L := by
  intro j _hj hdmod
  let d : ℤ := (j : ℤ) - (N + h + 1)
  let z : ℤ := carryOrbit h N d L
  have hzmod : z % (2 : ℤ) ^ (L + 2) =
      ((2 : ℤ) ^ (L + 1) - windowDiscrepancy h N L) %
        (2 : ℤ) ^ (L + 2) := by
    exact carryOrbit_emod_twoPow_add_two_of_modFourPulse hdmod L
  have hP : (0 : ℤ) < (2 : ℤ) ^ (L + 2) := by positivity
  have hzlarge : (N + h + L + 2 : ℤ) < |z| := by
    apply abs_gt_of_emod_mem_central hP
    · rw [hzmod]
      exact hcert.1
    · rw [hzmod]
      exact hcert.2
  refine ⟨L, Finset.mem_range.mpr (by omega), ?_⟩
  by_cases hz : 0 ≤ z
  · right
    rw [abs_of_nonneg hz] at hzlarge
    change (N + L + h + 2 : ℤ) ≤ z
    omega
  · left
    have hznonpos : z ≤ 0 := le_of_not_ge hz
    rw [abs_of_nonpos hznonpos] at hzlarge
    change z ≤ -(N + L + h + 2 : ℤ)
    omega

/-- Soundness of the restricted certificate: it rules out equality with any
integral tail state in the pulse class. -/
theorem tail_diff_ne_int_of_modFourPulseSurvivorKill
    {h N K : ℕ} (hkill : modFourPulseSurvivorKill h N K)
    {d : ℤ} (hdmod : d ≡ (2 : ℤ) [ZMOD 4]) :
    (d : ℝ) ≠ totientTail (N + h) - totientTail N := by
  intro hd
  have hboxR : |(d : ℝ)| < (N : ℝ) + h + 2 := by
    rw [hd]
    exact abs_tail_diff_lt h N
  have habs : |d| < (N : ℤ) + h + 2 := by exact_mod_cast hboxR
  have hlohi := abs_lt.mp habs
  have hmem :
      (d + ((N : ℤ) + h + 1)).toNat ∈
        Finset.range (2 * (N + h + 1) + 1) := by
    rw [Finset.mem_range]
    omega
  have hcand :
      (((d + ((N : ℤ) + h + 1)).toNat : ℤ)) -
          ((N : ℤ) + h + 1) = d := by
    omega
  have hcandMod :
      (((d + ((N : ℤ) + h + 1)).toNat : ℤ)) -
          ((N : ℤ) + h + 1) ≡ (2 : ℤ) [ZMOD 4] := by
    rwa [hcand]
  obtain ⟨i, _, hesc⟩ :=
    hkill (d + ((N : ℤ) + h + 1)).toNat hmem hcandMod
  rw [hcand] at hesc
  have htrack := carryOrbit_eq_tail_diff hd i
  have hstrip := abs_tail_diff_lt h (N + i)
  push_cast at hstrip
  rw [abs_lt] at hstrip
  rcases hesc with hlo | hhi
  · have hR : (carryOrbit h N d i : ℝ) ≤
        -((N : ℝ) + i + h + 2) := by
      exact_mod_cast hlo
    rw [htrack] at hR
    linarith [hstrip.1]
  · have hR : ((N : ℝ) + i + h + 2) ≤
        (carryOrbit h N d i : ℝ) := by
      exact_mod_cast hhi
    rw [htrack] at hR
    linarith [hstrip.2]

/-- **Pulse-prime survivor reduction for Erdős #249.**  It is enough to
kill the `2 mod 4` candidate states at one cofinal arithmetic-pulse prime for
each putative primitive period.  Every cell of the remaining producer is
finite and decidable. -/
theorem irrational_totientSeries_of_cofinal_modFourPulseSurvivorKill
    (hsupply : ∀ h : ℕ, 0 < h → ∀ B : ℕ,
      ∃ p : ℕ, B < p ∧ p.Prime ∧
        deltaTotient (4 * h) p ≡ (2 : ℤ) [ZMOD 4] ∧
          ∃ K : ℕ, modFourPulseSurvivorKill (4 * h) p K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h, hh, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨p, hpBound, _hp, hpulse, K, hkill⟩ :=
    hsupply h hh (N₀ + 3)
  have hpLarge : N₀ + 3 < p := hpBound
  have hint4 : ∀ N, N₀ ≤ N →
      totientTail (N + 4 * h) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := by
    intro N hN
    exact tail_diff_mul_mem_int hint 4 N hN
  obtain ⟨d, hd, hdmod⟩ :=
    integral_four_mul_tailDiff_mod_four_two_of_delta_pulse
      hpLarge hpulse hint4
  exact (tail_diff_ne_int_of_modFourPulseSurvivorKill hkill hdmod) hd

/-- Single-residue version of the preceding reduction.  Its finite cell is
one central-arc test modulo `2^(L+2)` at a cofinal pulse prime, so no explicit
candidate-state enumeration remains.  The supply ceiling is unchanged: the
two pulse bits exactly replace the two earlier recurrence steps. -/
theorem irrational_totientSeries_of_cofinal_modFourPulseCertificateSupply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ B : ℕ,
      ∃ p : ℕ, B < p ∧ p.Prime ∧
        deltaTotient (4 * h) p ≡ (2 : ℤ) [ZMOD 4] ∧
          ∃ L : ℕ, modFourPulseCertifiedKill (4 * h) p L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  apply irrational_totientSeries_of_cofinal_modFourPulseSurvivorKill
  intro h hh B
  obtain ⟨p, hpB, hp, hpulse, L, hcert⟩ := hsupply h hh B
  exact ⟨p, hpB, hp, hpulse, L,
    modFourPulseSurvivorKill_of_certifiedKill hcert⟩

#print axioms carryShift_dvd_iff_tailDiff_mem_int
#print axioms carrySectionsEventuallyPeriodicMod_of_shift_dvd
#print axioms not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
#print axioms not_totientAdjugateTailCost_lt_one
#print axioms idCoeff_mersenneModulus_does_not_annihilate_tailShift
#print axioms exists_prime_deltaTotient_four_mul_mod_four_two
#print axioms eventual_integral_four_mul_tailDiff_has_cofinal_mod_four_pulse
#print axioms integral_tailDiff_endpoint_modEq_neg_windowDiscrepancy
#print axioms integral_tailDiff_has_endpointSurvivor
#print axioms tail_diff_notMem_int_of_directedCertifiedKill
#print axioms irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply
#print axioms tail_diff_ne_int_of_modFourPulseSurvivorKill
#print axioms irrational_totientSeries_of_cofinal_modFourPulseSurvivorKill
#print axioms carryOrbit_emod_twoPow_add_two_of_modFourPulse
#print axioms modFourPulseSurvivorKill_of_certifiedKill
#print axioms irrational_totientSeries_of_cofinal_modFourPulseCertificateSupply

end Erdos257PeriodNoncollapse
