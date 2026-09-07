import ErdosProblems.Erdos243.ReciprocalTailRigidity
import ErdosProblems.Erdos243.DynamicCancellation
import Mathlib.Tactic

/-!
# Paper-complete campaign, round 7: exact algebra and signed descent

Source candidates for the supplied 7 September 2026 paper snapshot.
These files have NOT been compiled in the return environment.  No result
is represented as a new kernel-checked theorem in theorem_coverage.json.

The original declarations are reused.  New statements below assemble the
combined paper environments, extend the natural second-order identity to
the displayed integer domain, and prove signed eventual descent.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

/-- Short note `res:update`, `res:defect`: both identities, on the displayed
integer domain.  The next state is explicit rather than an extra premise. -/
theorem error_identities (a aNext D C : ℤ) :
    nextTailState a D C = C - centeredState a D C ∧
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := by
  exact ⟨nextTailState_eq_sub_centered a D C,
    sylvesterDefect_mul_nextTailState a aNext D C⟩

/-- Long record `res:scale`: a single declaration covering all three
homogeneity assertions, not just one of their existing component lemmas. -/
theorem state_scale (s a D C : ℤ) :
    nextDenState a (s * D) = s * nextDenState a D ∧
    nextTailState a (s * D) (s * C) = s * nextTailState a D C ∧
    centeredState a (s * D) (s * C) = s * centeredState a D C := by
  simp only [nextDenState, nextTailState, centeredState]
  constructor
  · ring
  constructor <;> ring

/-- Long record `res:secondorder`: the paper quantifies over integers.
The supplied `reducedStep_secondOrder` only quantifies over naturals. -/
theorem reduced_second_order_int
    (a aNext u uNext uNextNext v vNext h hNext : ℤ)
    (hu : h * uNext + v = a * u)
    (hv : h * vNext = a * v)
    (huNext : hNext * uNextNext + vNext = aNext * uNext) :
    a ^ 2 * u + h * hNext * uNextNext =
      h * (a + aNext) * uNext := by
  linear_combination -a * hu - hv + h * huNext

/-- The corresponding polynomial identity in an arbitrary commutative
ring.  This is supporting generality, not a replacement paper claim. -/
theorem reduced_second_order_ring {R : Type*} [CommRing R]
    (a aNext u uNext uNextNext v vNext h hNext : R)
    (hu : h * uNext + v = a * u)
    (hv : h * vNext = a * v)
    (huNext : hNext * uNextNext + vNext = aNext * uNext) :
    a ^ 2 * u + h * hNext * uNextNext =
      h * (a + aNext) * uNext := by
  linear_combination -a * hu - hv + h * huNext

/-- The scalar, signed, eventually nonnegative half of short-note
`res:absorb`/`res:descent`.  Exact denominator dynamics are NOT assumed.
Even positivity of C is unnecessary for this natural-valued version. -/
theorem signed_eventually_nonnegative_descent
    (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hstep : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n)
    (hnonneg : ∃ N, ∀ n, N ≤ n → 0 ≤ E n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  obtain ⟨N, hN⟩ := hnonneg
  have hmono : ∀ k, C (N + (k + 1)) ≤ C (N + k) := by
    intro k
    have hs := hstep (N + k)
    have he := hN (N + k) (by omega)
    have hidx : N + k + 1 = N + (k + 1) := by omega
    rw [hidx] at hs
    omega
  obtain ⟨K, hK⟩ :=
    antitone_nat_eventually_constant (fun k ↦ C (N + k)) hmono
  refine ⟨N + K, fun n hn ↦ ?_⟩
  have hNn : N ≤ n := by omega
  let k := n - N
  have hk : K ≤ k := by dsimp [k]; omega
  have hNk : N + k = n := Nat.add_sub_of_le hNn
  have hc := hK k hk
  have hcs := hK (k + 1) (by omega)
  change C (N + k) = C (N + K) at hc
  change C (N + (k + 1)) = C (N + K) at hcs
  have hsucc : C (n + 1) = C n := by
    rw [← hNk]
    simpa only [Nat.add_assoc] using hcs.trans hc.symm
  have hs := hstep n
  rw [hsucc] at hs
  omega

/-- Absorption only needs strict centring at the next index.  This local
form allows the eventual-centred frontier assembly without globally
strengthening its assumptions. -/
theorem zero_absorbing_at
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hzero : E n = 0)
    (hnext : Int.natAbs (E (n + 1)) < C (n + 1)) :
    E (n + 1) = 0 := by
  have hid := sylvesterDefect_mul_nextTailState
    (a n : ℤ) (a (n + 1) : ℤ) (D n : ℤ) (C n : ℤ)
  rw [← natTail_eq_nextTailState a C D hC n,
    ← natDen_eq_nextDenState a D hD n,
    ← hE n, ← hE (n + 1), hzero] at hid
  have hdiv : (C (n + 1) : ℤ) ∣ E (n + 1) := by
    refine ⟨-sylvesterDefect (a n : ℤ) (a (n + 1) : ℤ), ?_⟩
    nlinarith [hid]
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
  simpa using hnext

/-- The two independent assertions of short-note `res:absorb`/`res:descent`.
The scalar assertion retains its independent quantifiers. -/
theorem absorption_and_descent :
    (∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      (∀ n, Int.natAbs (E n) < C n) →
      ∀ n, E n = 0 → E (n + 1) = 0) ∧
    (∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      (∃ N, ∀ n, N ≤ n → 0 ≤ E n) →
      ∃ N, ∀ n, N ≤ n → E n = 0) := by
  constructor
  · intro a C D E hC hD hE hcentered n hn
    exact centeredState_zero_absorbing a C D E hC hD hE hcentered n hn
  · exact signed_eventually_nonnegative_descent

/-- Both local and eventual assertions of short-note
`res:step`/`res:eventual`, using the supplied integer declarations. -/
theorem two_zero_errors :
    (∀ a aNext D C : ℤ,
      nextTailState a D C ≠ 0 →
      centeredState a D C = 0 →
      centeredState aNext (nextDenState a D) (nextTailState a D C) = 0 →
      aNext = sylvesterNext a) ∧
    (∀ a D C : ℕ → ℤ,
      (∀ n, D (n + 1) = nextDenState (a n) (D n)) →
      (∀ n, C (n + 1) = nextTailState (a n) (D n) (C n)) →
      (∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0) →
      (∃ N, ∀ n, N ≤ n → C (n + 1) ≠ 0) →
      ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n)) := by
  exact ⟨sylvesterNext_eq_of_centered_zero,
    sylvesterNext_eventually_of_centered_zero⟩

/-- Assembly from signed zero error to the natural multiplier conclusion.
This helper is used by the state-level frontier, not counted as a canonical
rational-tail construction. -/
theorem natural_sylvester_of_eventual_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hzero : ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  obtain ⟨N, hN⟩ := hzero
  refine ⟨N, fun n hn ↦ ?_⟩
  apply sylvesterNext_eq_of_centered_zero (a n : ℤ) (a (n + 1) : ℤ)
    (D n : ℤ) (C n : ℤ)
  · rw [← natTail_eq_nextTailState a C D hC n]
    exact_mod_cast (hCpos (n + 1)).ne'
  · rw [← hE n]
    exact hN n hn
  · rw [← natDen_eq_nextDenState a D hD n,
      ← natTail_eq_nextTailState a C D hC n, ← hE (n + 1)]
    exact hN (n + 1) (by omega)

/-- Shifted multiplier hypothesis needed when the original sequence starts
with a_0=1.  This is only an assembly of the supplied bounded-negative
endpoint, not a new rigidity theorem. -/
theorem bounded_negative_endpoint_eventual_multiplier
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∃ N, ∀ n, N ≤ n → 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  obtain ⟨Na, hNa⟩ := ha
  have hshiftbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E (Na + n) := by
    obtain ⟨N, B, hN⟩ := hbound
    exact ⟨N, B, fun n hn ↦ hN (Na + n) (by omega)⟩
  have hshiftvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E (Na + n)) < C (Na + n) := by
    intro K
    obtain ⟨N, hN⟩ := hvanish K
    exact ⟨N, fun n hn ↦ hN (Na + n) (by omega)⟩
  obtain ⟨K, hK⟩ := boundedNegativePart_sylvesterNext_eventually
    (fun n ↦ a (Na + n)) (fun n ↦ C (Na + n)) (fun n ↦ D (Na + n))
    (fun n ↦ E (Na + n)) (fun n ↦ hNa (Na + n) (by omega))
    (fun n ↦ hCpos (Na + n))
    (fun n ↦ by simpa only [Nat.add_assoc] using hC (Na + n))
    (fun n ↦ by simpa only [Nat.add_assoc] using hD (Na + n))
    (fun n ↦ hE (Na + n)) hshiftbound hshiftvanish
  refine ⟨Na + K, fun n hn ↦ ?_⟩
  have hNn : Na ≤ n := by omega
  have hnK : K ≤ n - Na := by omega
  have hidx : Na + (n - Na) = n := Nat.add_sub_of_le hNn
  simpa only [← Nat.add_assoc, hidx] using hK (n - Na) hnK

end ErdosProblems.Erdos243.PaperCompleteR7
