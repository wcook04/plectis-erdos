-- Generated direct-prime emitted certificate shard from manifest: b2_L105_A75047.
import Erdos249257.CertificateKernel

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F105_A75047_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (105 : Nat).factorization.support) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have hsupport :
      (105 : Nat).factorization.support = ({3, 5, 7} : Finset Nat) := by
    rw [Nat.support_factorization]
    rw [show (105 : Nat) = 3 * (5 * (7)) by decide]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 3)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 5)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 7)]
    rfl
  rw [hsupport] at hp
  simpa using hp

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A75047_p3_prime_witness :
    PrimeComponentWitness 105 75047 2 3 7 := by
  refine ⟨(by decide : Nat.Prime 7), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 105 3 = 1180591620751771041793 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 105 3 = 1180591620751771041793 := by decide
    rw [hquot]
    have hfactor : (1180591620751771041793 : Nat).factorization 7 = 2 := by
      rw [show (1180591620751771041793 : Nat) = 7 ^ 2 * 24093706545954511057 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      change (7 ^ 2 : Nat).factorization 7 + (24093706545954511057 : Nat).factorization 7 = 2
      have hleft : (7 ^ 2 : Nat).factorization 7 = 2 :=
        Nat.factorization_pow_self (by decide : Nat.Prime 7)
      have hright : (24093706545954511057 : Nat).factorization 7 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 24093706545954511057)
      rw [hleft, hright]
    rw [hfactor]
    have hA_factor : (75047 : Nat).factorization 7 = 1 := by
      rw [show (75047 : Nat) = 7 * 10721 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 10721),
      ]
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F105_A75047_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 75047 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A75047_p3_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A75047_p5_prime_witness :
    PrimeComponentWitness 105 75047 2 5 31 := by
  refine ⟨(by decide : Nat.Prime 31), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
    rw [hquot]
    have hfactor : (19342822337210501698682881 : Nat).factorization 31 = 1 := by
      rw [show (19342822337210501698682881 : Nat) = 31 * 623962010877758119312351 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 31),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 623962010877758119312351),
      ]
    rw [hfactor]
    have hA_factor : (75047 : Nat).factorization 31 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 75047)
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F105_A75047_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 75047 2 5 := by
  exact Or.inr (Or.inr ⟨31, concrete_generated_b2_F105_A75047_p5_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A75047_p7_prime_witness :
    PrimeComponentWitness 105 75047 2 7 127 := by
  refine ⟨(by decide : Nat.Prime 127), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
    rw [hquot]
    have hfactor : (1237977819370199922113544193 : Nat).factorization 127 = 1 := by
      rw [show (1237977819370199922113544193 : Nat) = 127 * 9747856845434645056012159 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 127),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 127 ∣ 9747856845434645056012159),
      ]
    rw [hfactor]
    have hA_factor : (75047 : Nat).factorization 127 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 127 ∣ 75047)
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F105_A75047_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 75047 2 7 := by
  exact Or.inr (Or.inr ⟨127, concrete_generated_b2_F105_A75047_p7_prime_witness⟩)

def emittedCertificate_b2_L105_A75047 :
    EmittedCertificateTable 105 75047 2 where
  rows := ({3, 5, 7} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F105_A75047_factorization_support_cases hp with rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A75047_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A75047_p5_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A75047_p7_prime_witness

set_option maxRecDepth 10000 in
theorem orderOf_b2_mod540525526767270388528448873_eq_105_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 540525526767270388528448873)) = 105 := by
  let hcop : Nat.Coprime 2 540525526767270388528448873 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 105 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 105 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 540525526767270388528448873)ˣ) :
          ZMod 540525526767270388528448873) ^ 105) =
        (1 : ZMod 540525526767270388528448873)
      rw [ZMod.coe_unitOfCoprime]
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    105 75047 40564819207303340847894502572031 540525526767270388528448873 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L105_A75047

end Erdos249257
