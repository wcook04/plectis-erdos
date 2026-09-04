import ErdosProblems.Erdos243.SparseResetRecovery

/-!
# Erdős #243: clean-recovery length counterexample

This module will certify the finite exact primitive-orbit witness discovered by
`check_erdos243_clean_recovery_length.py`.
-/

namespace ErdosProblems.Erdos243

/-- The two coordinates of the exact reduced rational-tail state. -/
structure CleanRecoveryWitnessState where
  u : ℕ
  v : ℕ
deriving DecidableEq

/-- The nearest-integer quotient used by the centered primitive cocycle. -/
def cleanRecoveryWitnessNearest (s : CleanRecoveryWitnessState) : ℕ :=
  (2 * s.v + s.u) / (2 * s.u)

/-- The next displayed denominator selected by the centered quotient. -/
def cleanRecoveryWitnessMultiplier (s : CleanRecoveryWitnessState) : ℕ :=
  cleanRecoveryWitnessNearest s + 1

/-- Common content removed from the raw successor pair. -/
def cleanRecoveryWitnessPayment (s : CleanRecoveryWitnessState) : ℕ :=
  let a := cleanRecoveryWitnessMultiplier s
  Nat.gcd (a * s.u - s.v) (a * s.v)

/-- One exact centered, dynamically reduced primitive-tail step. -/
def cleanRecoveryWitnessStep
    (s : CleanRecoveryWitnessState) : CleanRecoveryWitnessState :=
  let a := cleanRecoveryWitnessMultiplier s
  let h := cleanRecoveryWitnessPayment s
  ⟨(a * s.u - s.v) / h, (a * s.v) / h⟩

/-- The exact witness orbit, started immediately before its small reset. -/
def cleanRecoveryWitnessOrbit (n : ℕ) : CleanRecoveryWitnessState :=
  (cleanRecoveryWitnessStep^[n]) ⟨11, 362⟩

def cleanRecoveryWitnessU (n : ℕ) : ℕ :=
  (cleanRecoveryWitnessOrbit n).u

def cleanRecoveryWitnessH (n : ℕ) : ℕ :=
  cleanRecoveryWitnessPayment (cleanRecoveryWitnessOrbit n)

/-- Absolute magnitude of the negative centered remainder at one witness
state.  It is written with natural subtraction because the certified orbit is
on the negative branch. -/
def cleanRecoveryWitnessNegativeMagnitude (n : ℕ) : ℕ :=
  cleanRecoveryWitnessNearest (cleanRecoveryWitnessOrbit n) *
      cleanRecoveryWitnessU n -
    (cleanRecoveryWitnessOrbit n).v

/-- The scale-free negative coordinate used by normalized-mass descent
proposals. -/
def cleanRecoveryWitnessNormalizedNegativeMass (n : ℕ) : ℚ :=
  cleanRecoveryWitnessNegativeMagnitude n / cleanRecoveryWitnessU n

/-- Every displayed state in the first return is primitive. -/
theorem cleanRecoveryWitness_primitive
    {n : ℕ} (hn : n ≤ 9) :
    Nat.Coprime
      (cleanRecoveryWitnessOrbit n).u
      (cleanRecoveryWitnessOrbit n).v := by
  interval_cases n <;> native_decide

/-- All nine centered remainders in the recovery are exactly `-1`. -/
theorem cleanRecoveryWitness_centeredError_neg_one
    {n : ℕ} (hn : n < 9) :
    (cleanRecoveryWitnessOrbit n).v + 1 =
      cleanRecoveryWitnessNearest (cleanRecoveryWitnessOrbit n) *
        (cleanRecoveryWitnessOrbit n).u := by
  interval_cases n <;> native_decide

/-- The exact height and payment lists found by the independent checker. -/
theorem cleanRecoveryWitness_values :
    (List.range 10).map cleanRecoveryWitnessU =
      [11, 3, 4, 5, 6, 7, 8, 9, 10, 11] ∧
    (List.range 9).map cleanRecoveryWitnessH =
      [4, 1, 1, 1, 1, 1, 1, 1, 1] := by
  native_decide

/-- The complete recovery returns not only to the same height but to the same
normalized negative state: both endpoints have magnitude one over height
eleven. -/
theorem cleanRecoveryWitness_normalizedNegativeMass_endpoint_values :
    cleanRecoveryWitnessU 0 = 11 ∧
      cleanRecoveryWitnessNegativeMagnitude 0 = 1 ∧
      cleanRecoveryWitnessU 9 = 11 ∧
      cleanRecoveryWitnessNegativeMagnitude 9 = 1 := by
  native_decide

/-- **Complete-recovery normalized return.**  The exact nine-step primitive
orbit returns from normalized negative mass `1/11` to `1/11`.  Consequently
no strict Lyapunov law depending only on this normalized coordinate can hold
across every complete clean recovery. -/
theorem cleanRecoveryWitness_normalizedNegativeMass_return :
    cleanRecoveryWitnessNormalizedNegativeMass 0 = 1 / 11 ∧
      cleanRecoveryWitnessNormalizedNegativeMass 9 = 1 / 11 := by
  rcases cleanRecoveryWitness_normalizedNegativeMass_endpoint_values with
    ⟨hu0, hm0, hu9, hm9⟩
  simp [cleanRecoveryWitnessNormalizedNegativeMass, hu0, hm0, hu9, hm9]

/-- The actual primitive orbit has a complete clean first recovery from zero
to nine. -/
theorem cleanRecoveryWitness_isCleanRecovery :
    CleanRecoveryAt cleanRecoveryWitnessU cleanRecoveryWitnessH 0 9 := by
  refine ⟨?_, ⟨by norm_num, ?_, ?_⟩, ?_⟩
  · change 1 < cleanRecoveryWitnessH 0
    native_decide
  · native_decide
  · intro k hk0 hk9
    interval_cases k <;> native_decide
  · intro k hk0 hk9
    interval_cases k <;> native_decide

/-- Complete-recovery length cannot force even a linear payment lower bound:
this length-nine recovery pays only four (and hence much less than `2^9`). -/
theorem cleanRecoveryWitness_payment_lt_length_and_exponential :
    cleanRecoveryWitnessH 0 < 9 ∧
      cleanRecoveryWitnessH 0 < 2 ^ 9 := by
  native_decide

/-! ## Periodic negative-unit transition kernel

The finite witness is one member of an infinite congruence family.  On a
negative-unit state `(u, u*q-1)`, a step with prescribed payment `h` has raw
next quotient numerator `(q+1)(u*q-1)+h`.  The following identity is the
algebraic propagation mechanism used by the exact family checker.
-/

/-- Numerator of the next quotient on a negative-unit state after dividing
the raw successor pair by the prescribed payment. -/
def negativeUnitTransitionNumerator (u h q : ℤ) : ℤ :=
  (q + 1) * (u * q - 1) + h

/-- Shifting the quotient by `(u+1)M*k` preserves its next quotient modulo
`M`.  This is an integer identity, so it has no finite-horizon hypothesis. -/
theorem negativeUnitTransitionNumerator_periodic
    (u h r M k : ℤ) :
    negativeUnitTransitionNumerator u h (r + (u + 1) * M * k) =
      negativeUnitTransitionNumerator u h r +
        (u + 1) * M * k *
          (u * ((r + (u + 1) * M * k) + r) + (u - 1)) := by
  simp only [negativeUnitTransitionNumerator]
  ring

/-- If the base residue produces quotient `rNext`, every periodic lift
produces a quotient congruent to `rNext` modulo `M`. -/
theorem negativeUnitTransitionQuotient_periodic
    (u h r rNext M k : ℤ)
    (hbase : negativeUnitTransitionNumerator u h r = (u + 1) * rNext) :
    negativeUnitTransitionNumerator u h (r + (u + 1) * M * k) =
      (u + 1) *
        (rNext + M * k *
          (u * ((r + (u + 1) * M * k) + r) + (u - 1))) := by
  rw [negativeUnitTransitionNumerator_periodic, hbase]
  ring

/-- **Terminal parity barrier.**  Once the sixth quotient of the clean-return
pattern is a multiple of `990`, its last three exact negative-unit transition
equations force the terminal quotient to be even.  The starting family class
is odd, so no member can concatenate by returning directly to that class. -/
theorem negativeUnitRecovery_terminalQuotient_even
    (q6 q7 q8 q9 t : ℤ)
    (hq6 : q6 = 990 * t)
    (hq7step : 9 * q7 = q6 * (8 * q6 + 7))
    (hq8step : 10 * q8 = q7 * (9 * q7 + 8))
    (hq9step : 11 * q9 = q8 * (10 * q8 + 9)) :
    ∃ z : ℤ, q9 = 2 * z := by
  let A : ℤ := t * (7920 * t + 7)
  let B : ℤ := A * (990 * A + 8)
  have hq7 : q7 = 110 * A := by
    rw [hq6] at hq7step
    dsimp [A]
    nlinarith [hq7step]
  have hq8 : q8 = 11 * B := by
    rw [hq7] at hq8step
    dsimp [B]
    nlinarith [hq8step]
  have hq9 : q9 = B * (110 * B + 9) := by
    rw [hq8] at hq9step
    nlinarith [hq9step]
  refine ⟨(A * (495 * A + 4)) * (110 * B + 9), ?_⟩
  rw [hq9]
  dsimp [B]
  ring

/-- **Terminal residue rigidity.**  The source-family congruence certificate
actually puts `t = q₆ / 990` in the class `-36 mod 1152`.  Substitution into
the last three transition factors shows that the terminal quotient is
`41472` times an odd integer, hence is exactly `41472 mod 82944`.  The theorem
isolates the small algebraic consumer; the exact checker proves that every
parameter in the source family supplies the displayed form of `t`. -/
theorem negativeUnitRecovery_terminalQuotient_oddMultiple_41472
    (c : ℤ) :
    let t := 1152 * c - 36
    let A := t * (7920 * t + 7)
    let B := A * (990 * A + 8)
    let q9 := B * (110 * B + 9)
    ∃ z : ℤ, q9 = 41472 * (2 * z + 1) := by
  let d : ℤ := 32 * c - 1
  let e : ℤ := 285120 * d + 7
  let s : ℤ := 82114560 * c ^ 2 - 5132097 * c + 80188
  let xd : ℤ := 16 * c - 1
  let ye : ℤ := 142560 * d + 3
  let xr : ℤ := 2 * xd * ye + xd + ye
  let yf : ℤ := 495 * s + 15
  let xb : ℤ := 2 * xr * yf + xr + yf
  let b0 : ℤ := d * e * (990 * s + 31)
  let yg : ℤ := 28160 * b0
  let z : ℤ := 2 * xb * yg + xb + yg
  refine ⟨z, ?_⟩
  dsimp [d, e, s, xd, ye, xr, yf, xb, b0, yg, z]
  ring

/-- **Forced ascent after the terminal class.**  A quotient in the terminal
class `41472 * (2z+1)` is divisible by `12`.  Its successor `q+1` is therefore
coprime to `12`, even after squaring.  In the negative-unit transition at
height `11`, the dynamic payment `gcd(12,(q+1)^2)` is exactly one. -/
theorem negativeUnitRecovery_terminal_nextPayment_one (z : ℤ) :
    Int.gcd 12 ((41472 * (2 * z + 1) + 1) ^ 2) = 1 := by
  apply Int.isCoprime_iff_gcd_eq_one.mp
  let k : ℤ := 3456 * (2 * z + 1)
  refine ⟨-(12 * k ^ 2 + 2 * k), 1, ?_⟩
  dsimp [k]
  ring

/-- Consequently the next normalized height is `12/1=12`, strictly above the
return height `11`.  Direct switching into another same-height clean recovery
(whose intermediate heights are all below `11`) is impossible. -/
theorem negativeUnitRecovery_terminal_nextHeight_twelve (z : ℤ) :
    12 / Int.gcd 12 ((41472 * (2 * z + 1) + 1) ^ 2) = 12 := by
  rw [negativeUnitRecovery_terminal_nextPayment_one]

/-- **Full payment at height twelve.**  If the next quotient is `-1` modulo
`13`, the dynamic payment removes the entire height.  The exact computation
checker identifies precisely which source-parameter classes supply this
divisibility; this theorem is the parameter-free arithmetic consumer. -/
theorem negativeUnitRecovery_heightTwelve_fullPayment (t : ℤ) :
    Int.gcd 13 (((13 * t - 1) + 1) ^ 2) = 13 := by
  rw [show (13 * t - 1) + 1 = 13 * t by ring]
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨t.natAbs * (13 * t.natAbs), ?_⟩
    ring

/-- A full payment of `13` at height `12` collapses the next primitive
numerator to one.  A primitive rational tail with numerator one is integral,
so its centered state is zero and the Sylvester tail is absorbing. -/
theorem negativeUnitRecovery_heightTwelve_collapse (t : ℤ) :
    13 / Int.gcd 13 (((13 * t - 1) + 1) ^ 2) = 1 := by
  rw [negativeUnitRecovery_heightTwelve_fullPayment]

/-- **Full payment on the error-minus-four height-thirteen branch.**  The
second exact residue checker identifies source classes whose multiplier is a
multiple of `17`; the dynamic payment then removes the whole primitive height
`13 - (-4) = 17`. -/
theorem negativeFourHeightThirteen_fullPayment (t : ℤ) :
    Int.gcd 17 ((17 * t) ^ 2) = 17 := by
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨t.natAbs * (17 * t.natAbs), ?_⟩
    ring

/-- Full payment `17` collapses the error-minus-four branch to primitive
height one, after which the centered rational tail is integral and absorbing. -/
theorem negativeFourHeightThirteen_collapse (t : ℤ) :
    17 / Int.gcd 17 ((17 * t) ^ 2) = 1 := by
  rw [negativeFourHeightThirteen_fullPayment]

/-- **Payment-seven boundary cascade.**  The exact source-cylinder checker
forces the height-13 multiplier into the class `7 mod 42`.  Writing it as
`7*(6z+1)` produces the height-two tie and then the height-three multiplier
`6*m^2+m+1`, where `m=546*z^2+168*z+13` is odd.  Its square therefore pays
the full factor four. -/
theorem paymentSevenCascade_finalFullPayment (z : ℤ) :
    let m : ℤ := 546 * z ^ 2 + 168 * z + 13
    Int.gcd 4 ((6 * m ^ 2 + m + 1) ^ 2) = 4 := by
  dsimp
  let n : ℤ :=
    894348 * z ^ 4 + 550368 * z ^ 3 + 127533 * z ^ 2 + 13188 * z + 514
  have hfactor :
      6 * (546 * z ^ 2 + 168 * z + 13) ^ 2 +
          (546 * z ^ 2 + 168 * z + 13) + 1 =
        2 * n := by
    dsimp [n]
    ring
  rw [hfactor, Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨n.natAbs * n.natAbs, ?_⟩
    ring

/-- The final payment four collapses the height-three state to primitive
height one, so the payment-seven boundary cylinder reaches the absorbing
zero-centered tail. -/
theorem paymentSevenCascade_finalCollapse (z : ℤ) :
    let m : ℤ := 546 * z ^ 2 + 168 * z + 13
    4 / Int.gcd 4 ((6 * m ^ 2 + m + 1) ^ 2) = 1 := by
  dsimp
  rw [paymentSevenCascade_finalFullPayment]

/-! ## Payment-one height-fourteen split

The remaining negative source cylinders have height-thirteen multiplier
`14*w+1`.  The exact residue checker proves that the actual family has only
`w = 0` or `3` modulo `15`.  The next identities are the small algebraic
consumers of that finite source-cylinder certificate.
-/

/-- On the `w = 3 mod 15` image, the height-fourteen multiplier is five
times `C = 3*d+2`.  After paying five, the new height is three and its
denominator has centered residue `+1`, so this branch cannot continue the
negative boundary excursion. -/
theorem paymentOneHeightFourteen_positiveSwitchIdentity (z : ℤ) :
    let d : ℤ := 2730 * z ^ 2 + 1104 * z + 111
    let C : ℤ := 3 * d + 2
    5 * C * (14 * C - 3) =
      3 * (210 * d ^ 2 + 265 * d + 83) + 1 := by
  dsimp
  ring

/-- On an even lift of the `w = 0 mod 15` image, the height-fifteen
multiplier has square `1 mod 16`.  Hence the payment at height fifteen is
one and the next height-sixteen centered residue is `-1`. -/
theorem paymentOneHeightSixteen_evenLiftSquare (z : ℤ) :
    let c : ℤ := 2 * z
    let m : ℤ := 2730 * c ^ 2 + 12 * c
    let D : ℤ := 210 * m ^ 2 + 13 * m + 1
    ∃ R : ℤ, D ^ 2 = 16 * R + 1 := by
  let r : ℤ := 1365 * z ^ 2 + 3 * z
  let x : ℤ := 1680 * r ^ 2 + 13 * r
  refine ⟨4 * x ^ 2 + x, ?_⟩
  dsimp [r, x]
  ring

/-- The odd lifts satisfy the same square congruence.  Here the multiplier
is `-1 mod 8`, rather than `+1 mod 8`, but its square is again `1 mod 16`.
Together with the even-lift theorem this covers every surviving cylinder. -/
theorem paymentOneHeightSixteen_oddLiftSquare (z : ℤ) :
    let c : ℤ := 2 * z + 1
    let m : ℤ := 2730 * c ^ 2 + 12 * c
    let D : ℤ := 210 * m ^ 2 + 13 * m + 1
    ∃ R : ℤ, D ^ 2 = 16 * R + 1 := by
  let r : ℤ := 1365 * z ^ 2 + 1368 * z + 342
  let x : ℤ := 1680 * r ^ 2 + 2533 * r + 955
  refine ⟨4 * x ^ 2 - x, ?_⟩
  dsimp [r, x]
  ring

/-! ## Height-sixteen modulus-seventeen split

The complete source-cylinder checker sharpens the surviving parameter image
to `c mod 17` in `{0,10,12}`.  The corresponding height-sixteen multipliers
are respectively `1`, `3`, and `0` modulo `17`.  These identities consume the
three finite residue branches without any orbit-horizon assumption.
-/

/-- A multiplier divisible by seventeen pays the entire error-minus-one
height `16-(-1)=17`. -/
theorem paymentOneHeightSixteen_fullPayment (z : ℤ) :
    Int.gcd 17 ((17 * z) ^ 2) = 17 :=
  negativeFourHeightThirteen_fullPayment z

/-- Full payment seventeen collapses the primitive numerator to one. -/
theorem paymentOneHeightSixteen_fullCollapse (z : ℤ) :
    17 / Int.gcd 17 ((17 * z) ^ 2) = 1 := by
  rw [paymentOneHeightSixteen_fullPayment]

/-- A multiplier in the class `3 mod 17` pays one and produces centered
error `+8` at height seventeen. -/
theorem paymentOneHeightSixteen_positiveSwitchIdentity (z : ℤ) :
    (17 * z + 3) * (16 * (17 * z + 3) - 17) =
      17 * (272 * z ^ 2 + 79 * z + 5) + 8 := by
  ring

/-- A multiplier in the class `1 mod 17` pays one and retains centered error
`-1` at height seventeen.  The exact checker proves that these are the only
source cylinders still capable of continuing negative support. -/
theorem paymentOneHeightSixteen_negativeSurvivorIdentity (z : ℤ) :
    (17 * z + 1) * (16 * (17 * z + 1) - 17) =
      17 * (272 * z ^ 2 + 15 * z) - 1 := by
  ring

/-! ## Height-seventeen rigidity and height-eighteen split

The next exact source certificate forces the height-seventeen multiplier to
`1 mod 18`, eliminating every nontrivial payment there.  At height eighteen
the source image modulo nineteen is only `0` or `1`, producing either a full
payment or another negative-unit survivor.
-/

/-- A multiplier in the class `1 mod 18` is coprime to eighteen even after
squaring, so the height-seventeen payment is exactly one. -/
theorem paymentOneHeightSeventeen_paymentOne (m : ℤ) :
    Int.gcd 18 ((18 * m + 1) ^ 2) = 1 := by
  apply Int.isCoprime_iff_gcd_eq_one.mp
  refine ⟨-(18 * m ^ 2 + 2 * m), 1, ?_⟩
  ring

/-- A height-eighteen multiplier divisible by nineteen pays the full factor
`18-(-1)=19`. -/
theorem paymentOneHeightEighteen_fullPayment (z : ℤ) :
    Int.gcd 19 ((19 * z) ^ 2) = 19 := by
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨z.natAbs * (19 * z.natAbs), ?_⟩
    ring

/-- Full payment nineteen collapses the primitive numerator to one. -/
theorem paymentOneHeightEighteen_fullCollapse (z : ℤ) :
    19 / Int.gcd 19 ((19 * z) ^ 2) = 1 := by
  rw [paymentOneHeightEighteen_fullPayment]

/-- The only nonterminal height-eighteen multiplier image is `1 mod 19`; it
pays one and retains centered error `-1` at height nineteen. -/
theorem paymentOneHeightEighteen_negativeSurvivorIdentity (z : ℤ) :
    (19 * z + 1) * (18 * (19 * z + 1) - 19) =
      19 * (342 * z ^ 2 + 17 * z) - 1 := by
  ring

/-! ## Height-nineteen payment-five cascade

The complete source cylinder has height-nineteen payment only one or five.
On the payment-five branch the quotient residue forces a height-four state;
the following identities prove that its next payment is the full factor five.
-/

/-- If the height-nineteen multiplier is `5*W` with `W=1 mod 4`, payment
five lands at height four with centered error `-1`, and its next multiplier
is itself divisible by five. -/
theorem paymentFiveHeightNineteen_heightFourIdentity (b : ℤ) :
    let W : ℤ := 4 * b + 1
    let X : ℤ := 76 * b ^ 2 + 34 * b + 4
    5 * W * (19 * W - 4) = 4 * (5 * X - 1) - 1 := by
  dsimp
  ring

/-- The induced height-four multiplier pays the full factor
`4-(-1)=5`. -/
theorem paymentFiveHeightNineteen_finalFullPayment (x : ℤ) :
    Int.gcd 5 ((5 * x) ^ 2) = 5 := by
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨x.natAbs * (5 * x.natAbs), ?_⟩
    ring

/-- Full payment five collapses every height-nineteen payment-five cylinder
to primitive height one and the absorbing centered-zero tail. -/
theorem paymentFiveHeightNineteen_finalCollapse (x : ℤ) :
    5 / Int.gcd 5 ((5 * x) ^ 2) = 1 := by
  rw [paymentFiveHeightNineteen_finalFullPayment]

/-! ## Height-twenty payment-seven cascade

The complete affine source-cylinder certificate leaves payments one and seven
at height twenty.  Every payment-seven cylinder lands at height three.  Its
quotient digit modulo five then either forces full payment five, switches to a
positive centered residue, or reaches height two and pays the full factor
three.  Thus no payment-seven cylinder can continue the negative boundary
mode to height twenty-one.
-/

/-- Writing the height-twenty multiplier as `7*W`, the source certificate
forces `W=1 mod 6`.  Payment seven therefore lands at height three with
centered error `-1`. -/
theorem heightTwentyPaymentSeven_heightThreeIdentity (c : ℤ) :
    let W : ℤ := 6 * c + 1
    let J : ℤ := 1680 * c ^ 2 + 518 * c + 41
    7 * W * (20 * W - 3) = 3 * (J - 1) - 1 := by
  dsimp
  ring

/-- On the unique positive-switch quotient digit, payment one at height four
produces centered error `+1` at height five. -/
theorem heightTwentyPaymentSeven_positiveSwitchIdentity (x : ℤ) :
    (5 * x + 3) * (4 * (5 * x + 3) - 5) =
      5 * (20 * x ^ 2 + 19 * x + 4) + 1 := by
  ring

/-- On either nonterminal negative quotient digit, the height-five multiplier
is `3 mod 6`.  Payment three lands at height two with centered error `-1` and
a multiplier divisible by three. -/
theorem heightTwentyPaymentSeven_heightFiveToHeightTwoIdentity (y : ℤ) :
    3 * (2 * y + 1) * (5 * (2 * y + 1) - 2) =
      2 * (6 * (5 * y ^ 2 + 4 * y + 1) - 1) - 1 := by
  ring

/-- The induced height-two multiplier pays the full factor
`2-(-1)=3`. -/
theorem heightTwentyPaymentSeven_finalFullPayment (x : ℤ) :
    Int.gcd 3 ((3 * x) ^ 2) = 3 := by
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨x.natAbs * (3 * x.natAbs), ?_⟩
    ring

/-- Full payment three collapses the last negative height-two branch to
primitive height one and the absorbing centered-zero tail. -/
theorem heightTwentyPaymentSeven_finalCollapse (x : ℤ) :
    3 / Int.gcd 3 ((3 * x) ^ 2) = 1 := by
  rw [heightTwentyPaymentSeven_finalFullPayment]

/-! ## Height-twenty-one payment-eleven split

The exact affine source cylinder restricts the height-twenty-one quotient
parameter to two classes.  The payment-one class reaches height twenty-two.
The payment-eleven class lands at height two with centered error `-1`; a
modulo-three refinement then either pays the full factor three or reaches
height three with centered error `-1`.
-/

/-- A height-twenty-one multiplier in the class `1 mod 22` pays one. -/
theorem heightTwentyOne_paymentOne (m : ℤ) :
    Int.gcd 22 ((22 * m + 1) ^ 2) = 1 := by
  apply Int.isCoprime_iff_gcd_eq_one.mp
  refine ⟨-(22 * m ^ 2 + 2 * m), 1, ?_⟩
  ring

/-- On the payment-eleven source class, the quotient multiplier is odd and
the reduced transition lands at height two with centered error `-1`. -/
theorem heightTwentyOnePaymentEleven_heightTwoIdentity (a : ℤ) :
    let B : ℤ := 9240 * a ^ 2 + 5059 * a + 692
    let W : ℤ := 2 * B + 1
    W * (231 * W - 22) = 2 * (462 * B ^ 2 + 440 * B + 105) - 1 := by
  dsimp
  ring

/-- The actual non-full-payment height-two residue is `1 mod 3`; payment one then
lands at height three with centered error `-1`. -/
theorem heightTwentyOnePaymentEleven_heightThreeIdentity (c : ℤ) :
    (3 * c + 1) * (2 * (3 * c + 1) - 3) =
      3 * (6 * c ^ 2 + c) - 1 := by
  ring

/-- The actual modulo-six refinement makes the height-three multiplier even. -/
theorem heightTwentyOnePaymentEleven_heightThreeMultiplierEven (z : ℤ) :
    6 * (2 * z) ^ 2 + 2 * z = 2 * (12 * z ^ 2 + z) := by
  ring

/-- Every even height-three multiplier pays the full factor four. -/
theorem heightTwentyOnePaymentEleven_fullPaymentFour (x : ℤ) :
    Int.gcd 4 ((2 * x) ^ 2) = 4 := by
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨x.natAbs * x.natAbs, ?_⟩
    ring

/-- Full payment four collapses the payment-eleven branch to height one. -/
theorem heightTwentyOnePaymentEleven_finalCollapse (x : ℤ) :
    4 / Int.gcd 4 ((2 * x) ^ 2) = 1 := by
  rw [heightTwentyOnePaymentEleven_fullPaymentFour]

/-! ## Height-twenty-two modulus-twenty-three split

The sole surviving height-twenty-two branch has centered error `-1`.  Its
next multiplier is a quadratic in the divided height-twenty-one quotient.
The exact affine source certificate isolates the two source residues that
make this multiplier divisible by twenty-three.
-/

/-- Payment one at height twenty one produces the stated height-twenty-two
multiplier and retains centered error `-1`. -/
theorem heightTwentyTwo_transitionIdentity (q : ℤ) :
    (22 * q + 1) * (21 * (22 * q + 1) - 22) =
      22 * ((462 * q ^ 2 + 20 * q + 1) - 1) - 1 := by
  ring

/-- The two source roots `11` and `19` modulo twenty-three force the
intermediate quotient parameter to be `12 mod 23`. -/
theorem heightTwentyTwo_sourceRootIdentity (s : ℤ) :
    9240 * s ^ 2 + 19 * s - 12 =
      17 * (s - 11) * (s - 19) + 23 * (401 * s ^ 2 + 23 * s - 155) := by
  ring

/-- At intermediate residue twelve, the height-twenty-two multiplier is
divisible by twenty-three. -/
theorem heightTwentyTwo_multiplierAtTwelveIdentity (z : ℤ) :
    462 * (23 * z + 12) ^ 2 + 20 * (23 * z + 12) + 1 =
      23 * (10626 * z ^ 2 + 11108 * z + 2903) := by
  ring

/-- A multiplier divisible by twenty-three pays the full factor
`22-(-1)=23`. -/
theorem heightTwentyTwo_fullPayment (x : ℤ) :
    Int.gcd 23 ((23 * x) ^ 2) = 23 := by
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨x.natAbs * (23 * x.natAbs), ?_⟩
    ring

/-- Full payment twenty-three collapses the corresponding height-twenty-two
cylinder to the absorbing height-one tail. -/
theorem heightTwentyTwo_fullCollapse (x : ℤ) :
    23 / Int.gcd 23 ((23 * x) ^ 2) = 1 := by
  rw [heightTwentyTwo_fullPayment]

/-- A payment-one multiplier in residue fifteen modulo twenty-three switches
the next centered error from `-1` to `+5`; it cannot carry negative support. -/
theorem heightTwentyTwo_positiveSwitchIdentity (z : ℤ) :
    (23 * z + 15) * (22 * (23 * z + 15) - 23) =
      23 * (506 * z ^ 2 + 637 * z + 200) + 5 := by
  ring

/-- Residue one modulo twenty-three is the only payment-one image that keeps
centered error `-1` at height twenty-three. -/
theorem heightTwentyTwo_negativeSurvivorIdentity (z : ℤ) :
    (23 * z + 1) * (22 * (23 * z + 1) - 23) =
      23 * (506 * z ^ 2 + 21 * z) - 1 := by
  ring

/-! ## Height-twenty-three singleton factor-twenty-four mode -/

/-- The exact source certificate puts the divided height-twenty-two quotient
in residue zero modulo twenty-four, forcing the height-twenty-three multiplier
to residue one. -/
theorem heightTwentyThree_actualMultiplierOneIdentity (w : ℤ) :
    506 * (24 * w) ^ 2 + 21 * (24 * w) + 1 =
      24 * (12144 * w ^ 2 + 21 * w) + 1 := by
  ring

/-- A height-twenty-three multiplier in residue one pays one and preserves
centered error `-1` at height twenty-four. -/
theorem heightTwentyThree_negativeSurvivorIdentity (c : ℤ) :
    (24 * c + 1) * (23 * (24 * c + 1) - 24) =
      24 * (552 * c ^ 2 + 22 * c) - 1 := by
  ring

/-! ## Height-twenty-four factor-twenty-five modes -/

/-- The factor-twenty-five multiplier differs from a polynomial with roots
one and three modulo five by an explicit multiple of five. -/
theorem heightTwentyFour_fullPaymentRootIdentity (c : ℤ) :
    (552 * c ^ 2 + 22 * c + 1) - 2 * (c - 1) * (c - 3) =
      5 * (110 * c ^ 2 + 6 * c - 1) := by
  ring

/-- Quotient residue one modulo five makes the multiplier divisible by five. -/
theorem heightTwentyFour_multiplierAtOneModFiveIdentity (z : ℤ) :
    552 * (5 * z + 1) ^ 2 + 22 * (5 * z + 1) + 1 =
      5 * (2760 * z ^ 2 + 1126 * z + 115) := by
  ring

/-- Quotient residue three modulo five makes the multiplier divisible by five. -/
theorem heightTwentyFour_multiplierAtThreeModFiveIdentity (z : ℤ) :
    552 * (5 * z + 3) ^ 2 + 22 * (5 * z + 3) + 1 =
      5 * (2760 * z ^ 2 + 3334 * z + 1007) := by
  ring

/-- A preceding quotient in residue two modulo five feeds the cofinal root
three of the factor-twenty-five multiplier. -/
theorem heightTwentyFour_precedingQuotientTwoIdentity (z : ℤ) :
    12144 * (5 * z + 2) ^ 2 + 21 * (5 * z + 2) =
      5 * (60720 * z ^ 2 + 48597 * z + 9723) + 3 := by
  ring

/-- A preceding quotient in residue four modulo five feeds the same cofinal
root three of the factor-twenty-five multiplier. -/
theorem heightTwentyFour_precedingQuotientFourIdentity (z : ℤ) :
    12144 * (5 * z + 4) ^ 2 + 21 * (5 * z + 4) =
      5 * (60720 * z ^ 2 + 97173 * z + 38877) + 3 := by
  ring

/-- Any multiplier divisible by five pays the full square factor twenty-five
at height twenty-four. -/
theorem heightTwentyFour_fullPayment (x : ℤ) :
    Int.gcd 25 ((5 * x) ^ 2) = 25 := by
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨x.natAbs * x.natAbs, ?_⟩
    ring

/-- Full payment twenty-five collapses a height-twenty-four cylinder to the
absorbing height-one tail. -/
theorem heightTwentyFour_fullCollapse (x : ℤ) :
    25 / Int.gcd 25 ((5 * x) ^ 2) = 1 := by
  rw [heightTwentyFour_fullPayment]

/-- If `25 * C = 24 * B^2 - 25 * B + 26` and the preceding
height-twenty-four multiplier `B` is odd, then the height-twenty-five
multiplier `C` is odd.  This is the parity obstruction behind the absence of
full factor-26 payment. -/
theorem heightTwentyFive_multiplierOdd (B C : ℤ)
    (hB : B % 2 = 1)
    (hC : 25 * C = 24 * B ^ 2 - 25 * B + 26) :
    C % 2 = 1 := by
  have hmod := congrArg (fun x : ℤ => x % 2) hC
  norm_num [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, hB] at hmod ⊢
  exact hmod

/-- An odd height-twenty-five multiplier cannot pay the full even factor 26. -/
theorem heightTwentyFive_noFullPaymentDivisibility (C : ℤ)
    (hC : C % 2 = 1) :
    ¬ (26 : ℤ) ∣ C ^ 2 := by
  intro h26
  have h2 : (2 : ℤ) ∣ C ^ 2 := dvd_trans (by norm_num) h26
  have hz : C ^ 2 % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h2
  norm_num [Int.mul_emod, pow_two, hC] at hz

/-- The actual payment-thirteen residue has reduced multiplier one, forcing
height-two multiplier 150. -/
theorem heightTwentyFivePaymentThirteen_heightTwoMultiplier :
    ((1 : ℤ) * (25 * 13 * 1 - 26) + 1) / 2 = 150 := by
  norm_num

/-- The forced height-two multiplier 150 pays the full factor three. -/
theorem heightTwentyFivePaymentThirteen_fullPaymentThree :
    Int.gcd 3 ((150 : ℤ) ^ 2) = 3 := by
  norm_num [Int.gcd_def]

/-- Full payment three collapses the factor-26 payment-thirteen branch to
height one. -/
theorem heightTwentyFivePaymentThirteen_finalCollapse :
    3 / Int.gcd 3 ((150 : ℤ) ^ 2) = 1 := by
  rw [heightTwentyFivePaymentThirteen_fullPaymentThree]

/-- On the actual factor-27 source image, the height-twenty-five multiplier
is `1 mod 702`; the exact divided transition has the displayed polynomial. -/
theorem heightTwentySix_multiplierAtOneMod702Identity (z : ℤ) :
    let C : ℤ := 702 * z + 1
    25 * C ^ 2 - 26 * C + 27 =
      26 * (473850 * z ^ 2 + 648 * z + 1) := by
  dsimp
  ring

/-- The resulting height-twenty-six multiplier is always one modulo 27. -/
theorem heightTwentySix_multiplierOneModTwentySeven (z : ℤ) :
    473850 * z ^ 2 + 648 * z + 1 =
      27 * (17550 * z ^ 2 + 24 * z) + 1 := by
  ring

/-! ## Height-twenty-seven uniform factor-twenty-eight activation -/

/-- After writing the rigid factor-27 multiplier as `D = 27*q+1`, the next
divided multiplier is the displayed quadratic polynomial in `q`. -/
theorem heightTwentySeven_multiplierQuotientIdentity (q : ℤ) :
    let D : ℤ := 27 * q + 1
    26 * D ^ 2 - 27 * D + 28 =
      27 * (702 * q ^ 2 + 25 * q + 1) := by
  dsimp
  ring

/-- The actual quotient class zero modulo twenty-eight preserves multiplier
one and hence centered error `-1` at height twenty-eight. -/
theorem heightTwentySeven_quotientZeroMode (z : ℤ) :
    702 * (28 * z) ^ 2 + 25 * (28 * z) + 1 =
      28 * (19656 * z ^ 2 + 25 * z) + 1 := by
  ring

/-- The actual quotient class four modulo twenty-eight forces multiplier
twenty-one.  Its payment is seven, leaving height four and centered error
`+1`; this is the uniform positive-switch mode. -/
theorem heightTwentySeven_quotientFourMode (z : ℤ) :
    702 * (28 * z + 4) ^ 2 + 25 * (28 * z + 4) + 1 =
      28 * (19656 * z ^ 2 + 5641 * z + 404) + 21 := by
  ring

/-- The actual quotient class twelve modulo twenty-eight also preserves
multiplier one and centered error `-1` at height twenty-eight. -/
theorem heightTwentySeven_quotientTwelveMode (z : ℤ) :
    702 * (28 * z + 12) ^ 2 + 25 * (28 * z + 12) + 1 =
      28 * (19656 * z ^ 2 + 16873 * z + 3621) + 1 := by
  ring

/-! ## Height-twenty-eight uniform factor-twenty-nine boundary killing -/

/-- Writing an actual surviving factor-28 multiplier as `E=28*q+1` turns
the next divided multiplier into one quadratic polynomial in `q`. -/
theorem heightTwentyEight_multiplierQuotientIdentity (q : ℤ) :
    let E : ℤ := 28 * q + 1
    27 * E ^ 2 - 28 * E + 29 =
      28 * (756 * q ^ 2 + 26 * q + 1) := by
  dsimp
  ring

/-- Quotient class zero modulo twenty-nine preserves multiplier one. -/
theorem heightTwentyEight_quotientZeroMode (z : ℤ) :
    756 * (29 * z) ^ 2 + 26 * (29 * z) + 1 =
      29 * (21924 * z ^ 2 + 26 * z) + 1 := by
  ring

/-- Quotient class fifteen modulo twenty-nine forces a multiplier divisible
by twenty-nine and therefore the full-payment branch. -/
theorem heightTwentyEight_quotientFifteenMode (z : ℤ) :
    756 * (29 * z + 15) ^ 2 + 26 * (29 * z + 15) + 1 =
      29 * (21924 * z ^ 2 + 22706 * z + 5879) := by
  ring

/-- Quotient class twenty-four gives multiplier eight modulo twenty-nine. -/
theorem heightTwentyEight_quotientTwentyFourMode (z : ℤ) :
    756 * (29 * z + 24) ^ 2 + 26 * (29 * z + 24) + 1 =
      29 * (21924 * z ^ 2 + 36314 * z + 15037) + 8 := by
  ring

/-- Quotient class twenty-five gives multiplier sixteen modulo twenty-nine. -/
theorem heightTwentyEight_quotientTwentyFiveMode (z : ℤ) :
    756 * (29 * z + 25) ^ 2 + 26 * (29 * z + 25) + 1 =
      29 * (21924 * z ^ 2 + 37826 * z + 16315) + 16 := by
  ring

/-- Quotient class twenty-seven gives multiplier fifteen modulo twenty-nine. -/
theorem heightTwentyEight_quotientTwentySevenMode (z : ℤ) :
    756 * (29 * z + 27) ^ 2 + 26 * (29 * z + 27) + 1 =
      29 * (21924 * z ^ 2 + 40850 * z + 19028) + 15 := by
  ring

/-- A multiplier divisible by twenty-nine pays the full factor twenty-nine. -/
theorem heightTwentyEight_fullPaymentTwentyNine (x : ℤ) :
    Int.gcd 29 ((29 * x) ^ 2) = 29 := by
  rw [Int.gcd_def]
  apply Nat.dvd_antisymm
  · exact Nat.gcd_dvd_left _ _
  · apply Nat.dvd_gcd (by simp)
    simp [pow_two, Int.natAbs_mul]
    refine ⟨x.natAbs * (29 * x.natAbs), ?_⟩
    ring

end ErdosProblems.Erdos243
