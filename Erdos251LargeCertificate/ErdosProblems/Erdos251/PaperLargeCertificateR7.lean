import ErdosProblems.Erdos251.PaperLargeStreamingV5

/-!
# Large finite certificate for res:cfexclusion

The prime census and Farey arithmetic are already kernel-checked by
`PaperLargeStreamingV5`. This module keeps the original R7 theorem names and
the printed bounds `2^39997` / `10^12040` by transporting
`PaperV5.LargeStreaming.printed_floor`. No `native_decide` or added axiom
enters the proof.
-/

namespace ErdosProblems.Erdos251.PaperR7.LargeCertificate

/-- Every rational presentation of the ACTUAL convergent prime series has
the printed large denominator bound, once this proof term is compiled. -/
theorem prime_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) :
    2 ^ 39997 ≤ b ∧ 10 ^ 12040 < b :=
  PaperV5.LargeStreaming.printed_floor a b hb (Or.inl hS)

/-- The gap series differs from the prime series by the integer 2. -/
theorem gap_denominator_floor (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeGapDyadicTerm n) = a / b) :
    2 ^ 39997 ≤ b ∧ 10 ^ 12040 < b :=
  PaperV5.LargeStreaming.printed_floor a b hb (Or.inr hS)

/-- The two series in the displayed theorem, in a single endpoint. -/
theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b ∨
      (∑' n, primeGapDyadicTerm n) = a / b) :
    2 ^ 39997 ≤ b ∧ 10 ^ 12040 < b :=
  PaperV5.LargeStreaming.printed_floor a b hb hS

#print axioms denominator_floor_both

end ErdosProblems.Erdos251.PaperR7.LargeCertificate
