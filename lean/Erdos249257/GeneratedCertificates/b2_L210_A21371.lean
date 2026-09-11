-- Generated direct-prime emitted certificate shard from manifest: b2_L210_A21371.
import Erdos249257.CertificateKernel

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F210_A21371_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (210 : Nat).factorization.support) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have hsupport :
      (210 : Nat).factorization.support = ({2, 3, 5, 7} : Finset Nat) := by
    rw [Nat.support_factorization]
    rw [show (210 : Nat) = 2 * (3 * (5 * (7))) by decide]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 2)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 3)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 5)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 7)]
    rfl
  rw [hsupport] at hp
  simpa using hp

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F210_A21371_p2_prime_witness :
    PrimeComponentWitness 210 21371 2 2 3 := by
  refine ⟨(by decide : Nat.Prime 3), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 210 2 = 40564819207303340847894502572033 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 210 2 = 40564819207303340847894502572033 := by decide
    rw [hquot]
    have hfactor : (40564819207303340847894502572033 : Nat).factorization 3 = 2 := by
      rw [show (40564819207303340847894502572033 : Nat) = 3 ^ 2 * 4507202134144815649766055841337 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      change (3 ^ 2 : Nat).factorization 3 + (4507202134144815649766055841337 : Nat).factorization 3 = 2
      have hleft : (3 ^ 2 : Nat).factorization 3 = 2 :=
        Nat.factorization_pow_self (by decide : Nat.Prime 3)
      have hright : (4507202134144815649766055841337 : Nat).factorization 3 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 4507202134144815649766055841337)
      rw [hleft, hright]
    rw [hfactor]
    have hA_factor : (21371 : Nat).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 21371)
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F210_A21371_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 210 21371 2 2 := by
  exact Or.inr (Or.inr ⟨3, concrete_generated_b2_F210_A21371_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F210_A21371_p3_prime_witness :
    PrimeComponentWitness 210 21371 2 3 3 := by
  refine ⟨(by decide : Nat.Prime 3), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 210 3 = 1393796574908163946347162983661240005427201 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 210 3 = 1393796574908163946347162983661240005427201 := by decide
    rw [hquot]
    have hfactor : (1393796574908163946347162983661240005427201 : Nat).factorization 3 = 1 := by
      rw [show (1393796574908163946347162983661240005427201 : Nat) = 3 * 464598858302721315449054327887080001809067 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 3),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 464598858302721315449054327887080001809067),
      ]
    rw [hfactor]
    have hA_factor : (21371 : Nat).factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 21371)
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F210_A21371_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 210 21371 2 3 := by
  exact Or.inr (Or.inr ⟨3, concrete_generated_b2_F210_A21371_p3_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F210_A21371_p5_prime_witness :
    PrimeComponentWitness 210 21371 2 5 11 := by
  refine ⟨(by decide : Nat.Prime 11), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 210 5 = 374144419156796217651873571134047410522241514864641 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 210 5 = 374144419156796217651873571134047410522241514864641 := by decide
    rw [hquot]
    have hfactor : (374144419156796217651873571134047410522241514864641 : Nat).factorization 11 = 1 := by
      rw [show (374144419156796217651873571134047410522241514864641 : Nat) = 11 * 34013129014254201604715779194004310047476501351331 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 11),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 34013129014254201604715779194004310047476501351331),
      ]
    rw [hfactor]
    have hA_factor : (21371 : Nat).factorization 11 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 21371)
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F210_A21371_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 210 21371 2 5 := by
  exact Or.inr (Or.inr ⟨11, concrete_generated_b2_F210_A21371_p5_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F210_A21371_p7_prime_witness :
    PrimeComponentWitness 210 21371 2 7 127 := by
  refine ⟨(by decide : Nat.Prime 127), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 210 7 = 1532495542293136552393534905231451066410343099426406401 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 210 7 = 1532495542293136552393534905231451066410343099426406401 := by decide
    rw [hquot]
    have hfactor : (1532495542293136552393534905231451066410343099426406401 : Nat).factorization 127 = 1 := by
      rw [show (1532495542293136552393534905231451066410343099426406401 : Nat) = 127 * 12066894033804224821996337836468118633152307869499263 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 127),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 127 ∣ 12066894033804224821996337836468118633152307869499263),
      ]
    rw [hfactor]
    have hA_factor : (21371 : Nat).factorization 127 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 127 ∣ 21371)
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F210_A21371_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 210 21371 2 7 := by
  exact Or.inr (Or.inr ⟨127, concrete_generated_b2_F210_A21371_p7_prime_witness⟩)

def emittedCertificate_b2_L210_A21371 :
    EmittedCertificateTable 210 21371 2 where
  rows := ({2, 3, 5, 7} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F210_A21371_factorization_support_cases hp with rfl | rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F210_A21371_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F210_A21371_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F210_A21371_p5_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F210_A21371_p7_prime_witness

set_option maxRecDepth 10000 in
theorem orderOf_b2_mod76997078158308270186466201046153689812490565047661778267213_eq_210_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 76997078158308270186466201046153689812490565047661778267213)) = 210 := by
  let hcop : Nat.Coprime 2 76997078158308270186466201046153689812490565047661778267213 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 210 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 210 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 76997078158308270186466201046153689812490565047661778267213)ˣ) :
          ZMod 76997078158308270186466201046153689812490565047661778267213) ^ 210) =
        (1 : ZMod 76997078158308270186466201046153689812490565047661778267213)
      rw [ZMod.coe_unitOfCoprime]
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    210 21371 1645504557321206042154969182557350504982735865633579863348609023 76997078158308270186466201046153689812490565047661778267213 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L210_A21371

end Erdos249257
