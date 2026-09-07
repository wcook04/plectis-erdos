import Erdos257PeriodNoncollapse.GenericTailOrbitRigidity
import Erdos257PeriodNoncollapse.TotientMahlerDefect
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Totient carry-kernel rigidity

This module connects the rationality-supplied tempered binary orbit to the
dyadic totient-kernel family.  Its role is deliberately structural: the carry
recurrence recovers every positive totient channel as a two-term difference
of carry sections.  No finite-state or finite-Cartier-rank conclusion is
claimed; the bridge preserves the coefficient-side rank rather than
compressing it.

This is infrastructure for Erdős #249, not a proof that the totient series is
irrational.
-/

namespace Erdos257PeriodNoncollapse

open Module

/-- The discrete derivative naturally recovered from a binary carry orbit. -/
def carryDerivative (u : ℕ → ℤ) (n : ℕ) : ℤ :=
  2 * u (n - 1) - u n

/-- Any exact binary-orbit recurrence recovers its coefficient at every
positive index through `carryDerivative`.  Temperedness is not needed. -/
theorem carryDerivative_eq_scaledCoeff_of_recurrence
    {c : ℕ → ℕ} {v : ℕ} {u : ℕ → ℤ}
    (hrec : ∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ))
    {n : ℕ} (hn : 0 < n) :
    carryDerivative u n = ((v * c n : ℕ) : ℤ) := by
  have h := hrec (n - 1)
  have hidx : n - 1 + 1 = n := by omega
  rw [hidx] at h
  simp only [carryDerivative]
  linarith

/-- A tempered totient orbit recovers the scaled totient sequence through its
discrete carry derivative. -/
theorem totient_temperedOrbit_derivative
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u)
    {n : ℕ} (hn : 0 < n) :
    carryDerivative u n = ((v * Nat.totient n : ℕ) : ℤ) :=
  carryDerivative_eq_scaledCoeff_of_recurrence hu.1 hn

/-- The carry derivative inherits Euler totient's multiplicativity on
coprime positive arguments. -/
theorem totient_carryDerivative_coprime_mul
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : Nat.Coprime m n) :
    (v : ℤ) * carryDerivative u (m * n) =
      carryDerivative u m * carryDerivative u n := by
  rw [totient_temperedOrbit_derivative hu (Nat.mul_pos hm hn),
    totient_temperedOrbit_derivative hu hm,
    totient_temperedOrbit_derivative hu hn]
  norm_cast
  rw [Nat.totient_mul hcop]
  ring

/-- GCD-corrected multiplicativity of the carry derivative.  Unlike the
coprime specialization, this identity retains the exact non-coprime defect. -/
theorem totient_carryDerivative_gcd_mul
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    carryDerivative u (m * n) * carryDerivative u (m.gcd n) =
      (m.gcd n : ℤ) * carryDerivative u m * carryDerivative u n := by
  have hg : 0 < m.gcd n := Nat.gcd_pos_of_pos_left n hm
  rw [totient_temperedOrbit_derivative hu (Nat.mul_pos hm hn),
    totient_temperedOrbit_derivative hu hg,
    totient_temperedOrbit_derivative hu hm,
    totient_temperedOrbit_derivative hu hn]
  norm_cast
  calc
    v * Nat.totient (m * n) * (v * Nat.totient (m.gcd n)) =
        v * v * (Nat.totient (m.gcd n) * Nat.totient (m * n)) := by ring
    _ = v * v * (Nat.totient m * Nat.totient n * m.gcd n) := by
      rw [Nat.totient_gcd_mul_totient_mul]
    _ = m.gcd n * (v * Nat.totient m) * (v * Nat.totient n) := by ring

/-- A dyadic section of an integer carry orbit, viewed over `ℚ`. -/
def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)

/-- Every positive-residue totient-kernel channel is a two-term difference of
adjacent carry-kernel channels.  This is the exact coefficient-to-carry bridge
used by rank-transfer arguments. -/
theorem totient_carryKernel_diff
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u)
    {j r : ℕ} (hr : 0 < r) :
    (fun n => (v : ℚ) * totientKernelSeq j r n) =
      fun n => 2 * carryKernelSeq u j (r - 1) n -
        carryKernelSeq u j r n := by
  funext n
  have hpos : 0 < 2 ^ j * n + r := by omega
  have h := totient_temperedOrbit_derivative hu hpos
  have hidx : 2 ^ j * n + r - 1 = 2 ^ j * n + (r - 1) := by omega
  simpa [carryDerivative, carryKernelSeq, totientKernelSeq, hidx] using
    congrArg (fun z : ℤ => (z : ℚ)) h.symm

/-! ## Canonical finite-level carry families -/

/-- The odd canonical dyadic channels through levels `1,...,e`. -/
abbrev TotientOddIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ j.val)

/-- The full carry-section family through levels `1,...,e`. -/
abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))

/-- The odd-residue part of the canonical totient family. -/
def canonicalTotientOddKernelFamily (e : ℕ) :
    TotientOddIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)

/-- Every carry section through levels `1,...,e`, without quotienting or
identifying residue channels. -/
def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val

/-- Embed an odd-channel index as its even predecessor carry section. -/
def carryEvenIndex {e : ℕ} : TotientOddIndex e → TotientCarryIndex e
  | ⟨j, r⟩ => ⟨j, ⟨2 * r.val, by
      rw [pow_succ]
      omega⟩⟩

/-- Embed an odd-channel index as the corresponding odd carry section. -/
def carryOddIndex {e : ℕ} : TotientOddIndex e → TotientCarryIndex e
  | ⟨j, r⟩ => ⟨j, ⟨2 * r.val + 1, by
      rw [pow_succ]
      omega⟩⟩

/-- The carry differences that recover the odd canonical totient channels. -/
def canonicalCarryDifferenceFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientOddIndex e → ℕ → ℚ := fun i =>
  2 • canonicalCarryKernelFamily u e (carryEvenIndex i) -
    canonicalCarryKernelFamily u e (carryOddIndex i)

/-- There are exactly `2^e-1` odd canonical channels through level `e`. -/
theorem card_totientOddIndex (e : ℕ) :
    Fintype.card (TotientOddIndex e) = 2 ^ e - 1 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  induction e with
  | zero => simp
  | succ e ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega

/-- Linear independence of the full canonical family restricts to the odd
canonical channels. -/
theorem linearIndependent_totientOddKernelFamily
    (e : ℕ)
    (hcanon : LinearIndependent ℚ (canonicalTotientKernelFamily e)) :
    LinearIndependent ℚ (canonicalTotientOddKernelFamily e) := by
  have hsub := hcanon.comp (fun i : TotientOddIndex e => Sum.inr i) (by
    intro i k hik
    exact Sum.inr.inj hik)
  simpa [Function.comp_def, canonicalTotientOddKernelFamily,
    canonicalTotientKernelFamily] using hsub

/-- A separated minor for the canonical family already certifies independence
of all its odd channels. -/
theorem linearIndependent_totientOddKernelFamily_of_certificate
    (e : ℕ)
    (cert : SeparatedMinorCertificate (canonicalTotientKernelFamily e)) :
    LinearIndependent ℚ (canonicalTotientOddKernelFamily e) :=
  linearIndependent_totientOddKernelFamily e
    (linearIndependent_of_separatedMinorCertificate
      (canonicalTotientKernelFamily e) cert)

/-- The recurrence identifies the canonical carry differences with the odd
totient channels, scaled by the orbit multiplier. -/
theorem canonicalCarryDifferenceFamily_eq_smul_totient
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (e : ℕ) :
    canonicalCarryDifferenceFamily u e =
      fun i => (v : ℚ) • canonicalTotientOddKernelFamily e i := by
  funext i
  rcases i with ⟨j, r⟩
  have h := totient_carryKernel_diff hu
    (j := j.val + 1) (r := 2 * r.val + 1) (by omega)
  simpa [canonicalCarryDifferenceFamily, canonicalCarryKernelFamily,
    canonicalTotientOddKernelFamily, carryEvenIndex, carryOddIndex,
    Pi.smul_apply, smul_eq_mul] using h.symm

/-- Every canonical carry difference lies in the span of the full finite-level
carry family. -/
theorem canonicalCarryDifferenceFamily_mem_span
    (u : ℕ → ℤ) (e : ℕ) (i : TotientOddIndex e) :
    canonicalCarryDifferenceFamily u e i ∈
      Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)) := by
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨carryEvenIndex i, rfl⟩
  · exact Submodule.subset_span ⟨carryOddIndex i, rfl⟩

/-- **Finite-level carry anti-compression.**  A nonzero-multiplier orbit whose
canonical totient family is linearly independent must retain at least
`2^e-1` dimensions among its carry sections through level `e`.  Temperedness
is not used beyond supplying the exact recurrence through the existing orbit
interface. -/
theorem finrank_canonicalCarryKernel_ge_of_linearIndependent
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (e : ℕ)
    (hcanon : LinearIndependent ℚ (canonicalTotientKernelFamily e)) :
    2 ^ e - 1 ≤
      finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  have hodd := linearIndependent_totientOddKernelFamily e hcanon
  let q : ℚˣ := Units.mk0 (v : ℚ) (by exact_mod_cast (Nat.ne_of_gt hv))
  have hscaled : LinearIndependent ℚ
      ((fun _ : TotientOddIndex e => q) • canonicalTotientOddKernelFamily e) :=
    hodd.units_smul (fun _ => q)
  have hscale_eq :
      ((fun _ : TotientOddIndex e => q) • canonicalTotientOddKernelFamily e) =
        (fun i => (v : ℚ) • canonicalTotientOddKernelFamily e i) := by
    funext i n
    simp [q]
  rw [hscale_eq] at hscaled
  have hdiff : LinearIndependent ℚ (canonicalCarryDifferenceFamily u e) := by
    rw [canonicalCarryDifferenceFamily_eq_smul_totient hu e]
    exact hscaled
  letI : Module.Finite ℚ
      (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  rw [← card_totientOddIndex e]
  have hrank := finrank_span_eq_card hdiff
  rw [← hrank]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact canonicalCarryDifferenceFamily_mem_span u e i

/-- Certificate-facing form of `finrank_canonicalCarryKernel_ge_of_linearIndependent`.
This is immediately usable with the existing finite separated-minor owner. -/
theorem finrank_canonicalCarryKernel_ge_of_certificate
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (e : ℕ)
    (cert : SeparatedMinorCertificate (canonicalTotientKernelFamily e)) :
    2 ^ e - 1 ≤
      finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) :=
  finrank_canonicalCarryKernel_ge_of_linearIndependent hv hu e
    (linearIndependent_of_separatedMinorCertificate
      (canonicalTotientKernelFamily e) cert)

/-- Rationality of the totient coefficient series, together with an all-level
canonical independence producer, yields one tempered integral carry whose
finite-level section ranks grow at least as `2^e-1`. -/
theorem not_irrational_totientSeries_implies_unbounded_carryRank
    (hcanon : ∀ e : ℕ,
      LinearIndependent ℚ (canonicalTotientKernelFamily e))
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e))) := by
  obtain ⟨v, hv, u, hu⟩ :=
    (not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
      Nat.totient Nat.totient_le).mp hirr
  exact ⟨v, hv, u, hu, fun e =>
    finrank_canonicalCarryKernel_ge_of_linearIndependent hv hu e (hcanon e)⟩

/-- **Unconditional anti-compression consequence of the CRT--Dirichlet
minor.**  If the totient series were rational, its tempered integral carry
would have unbounded dyadic section rank.

This is the strongest current consumer of the separated-minor producer.  It
does not by itself prove irrationality: a separate theorem bounding the
dyadic section rank of every rationality-supplied tempered carry is still
required, and no such finite-rank compression theorem follows from the
recurrence and temperedness alone. -/
theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e))) :=
  not_irrational_totientSeries_implies_unbounded_carryRank
    linearIndependent_canonicalTotientKernelFamily hirr

end Erdos257PeriodNoncollapse
