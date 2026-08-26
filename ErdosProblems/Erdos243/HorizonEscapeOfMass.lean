import ErdosProblems.Erdos243.FiniteHorizonResidue
import Mathlib.Tactic
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Erdős #243: the self-destruction clock and escape of mass

`FiniteHorizonResidue` proves that survival through `h` forced updates depends
only on the seed modulo `(h+1)!`, and records explicitly that it "neither
constructs an infinite negative-state orbit nor rules one out".  This file
supplies the exact interaction between the finite facts and the infinite
question.

## The clock

Set `D_n = (n+1)(a_n - 1) - 1`.  A one-line substitution in the forced update
gives the exact multiplicative law

`D_{n+1} = a_n · D_n`   (`forcedClock_forcedState_succ`)

so the clock at any later time is a multiple of the clock one step in.  Every
multiplier therefore installs a divisor of every later clock value, while
`D_n + 1 = (n+1)(a_n - 1)` is a multiple of `n+1`.  Reading those two facts at
`n = a₀ - 1` gives `a₀ ∣ 1`:

`not_forcedSurvives_of_two_le` — a seed `a₀ ≥ 2` cannot survive `a₀ - 1`
updates.  Equivalently every surviving horizon obeys `H ≤ a₀ - 2`.

## Escape of mass

The exceptional seed `1` is a fixed point (`forcedNumerator n 1 = n + 2`), so it
survives every horizon (`forcedSurvives_one`).  Factorial-residue transport then
gives arbitrarily large survivors at every horizon
(`factorialGhost_survives`): `1 + k·(H+1)!` survives `H` updates for every `k`.

Combining the two: for every `H`, the nontrivial survivor set is nonempty but
disjoint from `[2, H+1]` and contains `1 + (H+1)!`, so

`H + 2 ≤ min Sₕ ≤ 1 + (H+1)!`.

Finite-horizon survival is a factorial-adic ghost of the boundary fixed point
`1`; the Archimedean seed is forced to infinity.  There is no bounded diagonal
sequence of genuine seeds, which is exactly why finite satisfiability does not
yield a standard infinite orbit.

## Claim ceiling

**Erdős #243 remains open.**  This kills every bounded-seed and
finite-diagonal attack on the normalized constant-negative branch; it does not
exclude an unbounded orbit.
-/

namespace ErdosProblems.Erdos243

/-- The self-destruction clock of the forced orbit at index `n`. -/
def forcedClock (index : ℕ) (a : ℤ) : ℤ := (index + 1 : ℤ) * (a - 1) - 1

/-- The state reached after `remaining` forced updates. -/
def forcedState : ℕ → ℕ → ℤ → ℤ
  | 0, _, a => a
  | remaining + 1, index, a =>
      forcedState remaining (index + 1) (forcedNumerator index a / (index + 2 : ℤ))

/-- **The clock law.**  One forced update multiplies the clock by the current
multiplier.  This is an exact polynomial identity, not an estimate. -/
theorem forcedClock_forcedState_succ (index : ℕ) (a : ℤ)
    (hdvd : ((index : ℤ) + 2) ∣ forcedNumerator index a) :
    forcedClock (index + 1) (forcedNumerator index a / ((index : ℤ) + 2))
      = a * forcedClock index a := by
  obtain ⟨b, hb⟩ := hdvd
  have hd : ((index : ℤ) + 2) ≠ 0 := by omega
  have hq : forcedNumerator index a / ((index : ℤ) + 2) = b := by
    rw [hb, Int.mul_ediv_cancel_left _ hd]
  have hnum : ((index : ℤ) + 2) * b
      = (index + 1 : ℤ) * a ^ 2 - (index + 2 : ℤ) * a + (index + 3 : ℤ) := by
    rw [← hb, forcedNumerator]
  rw [hq, forcedClock, forcedClock]
  push_cast
  push_cast at hnum
  linear_combination hnum

/-- Survival is monotone in the horizon. -/
theorem forcedSurvives_of_succ : ∀ {r index : ℕ} {a : ℤ},
    ForcedSurvives (r + 1) index a → ForcedSurvives r index a
  | 0, _, _, _ => trivial
  | r + 1, index, a, hs => by
      obtain ⟨hdvd, hs'⟩ := hs
      exact ⟨hdvd, forcedSurvives_of_succ hs'⟩

theorem forcedSurvives_of_le {r s index : ℕ} {a : ℤ} (hrs : r ≤ s)
    (hs : ForcedSurvives s index a) : ForcedSurvives r index a := by
  induction s generalizing r with
  | zero => simpa [Nat.le_zero.mp hrs] using hs
  | succ s ih =>
      rcases Nat.lt_or_ge r (s + 1) with hlt | hge
      · exact ih (by omega) (forcedSurvives_of_succ hs)
      · simpa [Nat.le_antisymm hrs hge] using hs

/-- Any divisor of the clock persists through every later forced update. -/
theorem dvd_forcedClock_forcedState (c : ℤ) : ∀ (r index : ℕ) (a : ℤ),
    ForcedSurvives r index a → c ∣ forcedClock index a →
    c ∣ forcedClock (index + r) (forcedState r index a)
  | 0, index, a, _, hc => by simpa [forcedState] using hc
  | r + 1, index, a, hs, hc => by
      obtain ⟨hdvd, hs'⟩ := hs
      have hstep := forcedClock_forcedState_succ index a hdvd
      have hc' : c ∣ forcedClock (index + 1) (forcedNumerator index a / (index + 2 : ℤ)) := by
        rw [hstep]
        exact Dvd.dvd.mul_left hc a
      have := dvd_forcedClock_forcedState c r (index + 1)
        (forcedNumerator index a / (index + 2 : ℤ)) hs' hc'
      have harr : index + 1 + r = index + (r + 1) := by omega
      rw [harr] at this
      simpa [forcedState] using this

/-- **The current multiplier divides every later clock.** -/
theorem dvd_forcedClock_of_forcedSurvives {r index : ℕ} {a : ℤ}
    (hs : ForcedSurvives (r + 1) index a) :
    a ∣ forcedClock (index + (r + 1)) (forcedState (r + 1) index a) := by
  obtain ⟨hdvd, hs'⟩ := hs
  have hstep := forcedClock_forcedState_succ index a hdvd
  have hc : a ∣ forcedClock (index + 1) (forcedNumerator index a / (index + 2 : ℤ)) := by
    rw [hstep]; exact Dvd.intro _ rfl
  have := dvd_forcedClock_forcedState a r (index + 1)
    (forcedNumerator index a / (index + 2 : ℤ)) hs' hc
  have harr : index + 1 + r = index + (r + 1) := by omega
  rw [harr] at this
  simpa [forcedState] using this

/-- **The stop theorem.**  A seed at least `2` self-destructs by its own value:
it cannot survive `a₀ - 1` forced updates.  Equivalently, any surviving finite
horizon obeys `H ≤ a₀ - 2`. -/
theorem not_forcedSurvives_of_two_le {H : ℕ} {a : ℤ} (ha : 2 ≤ a)
    (hH : a ≤ (H : ℤ) + 1) : ¬ ForcedSurvives H 0 a := by
  intro hs
  set r : ℕ := (a - 1).toNat with hr
  have hrcast : (r : ℤ) = a - 1 := Int.toNat_of_nonneg (by omega)
  have hrle : r ≤ H := by omega
  have hrpos : 1 ≤ r := by omega
  obtain ⟨s, hs'⟩ : ∃ s : ℕ, r = s + 1 := ⟨r - 1, by omega⟩
  have hsurv : ForcedSurvives (s + 1) 0 a := by
    rw [← hs']; exact forcedSurvives_of_le hrle hs
  have hdvd := dvd_forcedClock_of_forcedSurvives hsurv
  rw [Nat.zero_add] at hdvd
  rw [← hs'] at hdvd
  have hclock : forcedClock r (forcedState r 0 a) = a * (forcedState r 0 a - 1) - 1 := by
    rw [forcedClock, hrcast]
    ring
  rw [hclock] at hdvd
  have hone : a ∣ 1 := by
    have hmul : a ∣ a * (forcedState r 0 a - 1) := Dvd.intro _ rfl
    have hsub := Dvd.dvd.sub hmul hdvd
    simpa using hsub
  have := Int.le_of_dvd one_pos hone
  omega

/-! ## The factorial-adic ghosts -/

@[simp] theorem forcedNumerator_one (n : ℕ) : forcedNumerator n 1 = (n : ℤ) + 2 := by
  rw [forcedNumerator]; ring

/-- The forbidden boundary seed `1` is a fixed point of every forced update, so
it survives every finite horizon. -/
theorem forcedSurvives_one : ∀ h index : ℕ, ForcedSurvives h index 1
  | 0, _ => trivial
  | h + 1, index => by
      have hd : ((index : ℤ) + 2) ≠ 0 := by omega
      have hnum : forcedNumerator index (1 : ℤ) = (index : ℤ) + 2 :=
        forcedNumerator_one index
      refine ⟨?_, ?_⟩
      · rw [hnum]
      · rw [hnum, Int.ediv_self hd]
        exact forcedSurvives_one h (index + 1)

/-- **Escape of mass.**  Every factorial neighbourhood of the forbidden fixed
seed supplies arbitrarily large finite-horizon survivors: the survivor set is
never empty, but its mass is forced to infinity. -/
theorem factorialGhost_survives (h : ℕ) (k : ℤ) :
    ForcedSurvives h 0 (1 + k * ((h + 1).factorial : ℤ)) := by
  have hmod : (1 + k * ((h + 1).factorial : ℤ)) ≡ 1 [ZMOD ((h + 1).factorial : ℤ)] := by
    have hcomm : (1 : ℤ) + k * ((h + 1).factorial : ℤ)
        = 1 + ((h + 1).factorial : ℤ) * k := by ring
    rw [Int.ModEq, hcomm, Int.add_mul_emod_self_left]
  exact (forcedSurvives_iff_of_modEq_factorial hmod).2 (forcedSurvives_one h 0)

/-- **The gap between the two facts.**  For every horizon the nontrivial
survivor set is nonempty but starts beyond the horizon: there is no bounded
diagonal sequence of genuine seeds. -/
theorem survivor_window (H : ℕ) :
    (∀ a : ℤ, 2 ≤ a → a ≤ (H : ℤ) + 1 → ¬ ForcedSurvives H 0 a) ∧
      ForcedSurvives H 0 (1 + ((H + 1).factorial : ℤ)) ∧
      2 ≤ 1 + ((H + 1).factorial : ℤ) := by
  refine ⟨fun a ha hle => not_forcedSurvives_of_two_le ha hle, ?_, ?_⟩
  · simpa using factorialGhost_survives H 1
  · have hfac : 1 ≤ (((H + 1).factorial : ℕ) : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero (H + 1))
    omega

end ErdosProblems.Erdos243
