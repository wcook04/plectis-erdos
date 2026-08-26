import ErdosProblems.Erdos243.DynamicCancellation
import ErdosProblems.Erdos243.FeedbackRealizability
import Mathlib.Tactic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Erdős #243: the canonical root kills the artificial square-residue branches

`FeedbackRealizability` distinguishes a true reduced feedback step from a bare
square-residue congruence, but the congruence it works against still carries a
free square root `t`.  That freedom is illusory.

## The orientation

Put `e = v - (a-1)u` and `q = a·u - v`.  The map `(u,v) ↦ (e,q)` is the
unimodular substitution `e + q = u`, `a·e + (a-1)·q = v`, so

`gcd(e, q) = gcd(u, v)`   (`centered_rawNext_gcd`)

and for a *reduced* state `e` is invertible modulo the whole raw next
numerator — including every cancellation factor.  The inverse substitution also
gives the canonical orientation `v ≡ a·e (mod q)`.  Against that orientation
the identity

`t² - h·e·e' = t·(t - a·e) + e·(a·t - h·e')`

converts the quadratic congruence into a *linear* one
(`orientedSquareRoot_iff_feedback`), and the linear one is equivalent to
existence and uniqueness of a transporting next multiplier
(`canonicalRoot_feedback_iff_existsUnique`).

## What this excludes

For `Q` odd squarefree with `r` prime factors, `t² ≡ 1 (mod Q)` has `2^r`
roots; exactly one of them satisfies the orientation.  The remaining `2^r - 1`
are artificial.  `fifteen_fake_root_four` is the smallest witness: `15 ∣ 4² - 1`
while `15 ∤ 16·4 + 1`, so deleting the orientation hypothesis from
`orientedSquareRoot_iff_feedback` produces a false nearby statement with a
two-line `decide` counterexample.

`rawNext_gcd_eq_gcd_denominator_sq` completes the picture: the cancellation
factor `gcd(q, a·v)` — already known to equal `gcd(q, a²)` — also equals
`gcd(q, v²)`.  The old denominator is therefore both the distinguished square
root *and* the exact carrier of the content to be removed; nothing about the
step is a free parameter.

## Claim ceiling

**Erdős #243 remains open.**  This classifies the local artificial
countermodels and makes the step deterministic; it does not exclude an
infinite orbit.
-/

namespace ErdosProblems.Erdos243

/-! ## The unimodular centring -/

/-- **Centring is unimodular.**  The centred error and the raw next numerator
have the same gcd as the original reduced pair, so for a primitive state the
centred error is a unit against the *entire* raw next numerator. -/
theorem centered_rawNext_gcd {a u v e q : ℤ}
    (he : e = v - (a - 1) * u) (hq : q = a * u - v) :
    Int.gcd e q = Int.gcd u v := by
  have hu : u = e + q := by rw [he, hq]; ring
  have hv : v = a * e + (a - 1) * q := by rw [he, hq]; ring
  have heq : (Int.gcd e q : ℤ) ∣ e := Int.gcd_dvd_left e q
  have heq' : (Int.gcd e q : ℤ) ∣ q := Int.gcd_dvd_right e q
  have huv : (Int.gcd u v : ℤ) ∣ u := Int.gcd_dvd_left u v
  have huv' : (Int.gcd u v : ℤ) ∣ v := Int.gcd_dvd_right u v
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd
    · rw [hu]; exact dvd_add heq heq'
    · rw [hv]
      exact dvd_add (Dvd.dvd.mul_left heq a) (Dvd.dvd.mul_left heq' (a - 1))
  · apply Int.dvd_gcd
    · rw [he]
      exact Dvd.dvd.sub huv' (Dvd.dvd.mul_left huv (a - 1))
    · rw [hq]
      exact Dvd.dvd.sub (Dvd.dvd.mul_left huv a) huv'

private theorem dvd_of_gcd_eq_one_mul_left {e q z : ℤ}
    (hcop : Int.gcd e q = 1) (hz : q ∣ e * z) : q ∣ z := by
  have hone : IsCoprime e q := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  exact (hone.symm.dvd_of_dvd_mul_left hz)

/-! ## The oriented congruence linearises -/

/-- **The free square root disappears.**  Once a root is oriented by
`t ≡ a·e (mod q)`, its quadratic norm condition is *equivalent* to the linear
feedback congruence.  Both directions are the same polynomial identity; the
forward one additionally cancels the unit `e`. -/
theorem orientedSquareRoot_iff_feedback {a e eNext h q t : ℤ}
    (hcop : Int.gcd e q = 1) (horient : q ∣ t - a * e) :
    q ∣ t ^ 2 - h * e * eNext ↔ q ∣ a * t - h * eNext := by
  constructor
  · intro hnorm
    refine dvd_of_gcd_eq_one_mul_left hcop ?_
    have hrw : e * (a * t - h * eNext)
        = (t ^ 2 - h * e * eNext) - t * (t - a * e) := by ring
    rw [hrw]
    exact Dvd.dvd.sub hnorm (Dvd.dvd.mul_left horient t)
  · intro hlinear
    have hrw : t ^ 2 - h * e * eNext
        = t * (t - a * e) + e * (a * t - h * eNext) := by ring
    rw [hrw]
    exact dvd_add (Dvd.dvd.mul_left horient t) (Dvd.dvd.mul_left hlinear e)

/-- Linear feedback divisibility is exactly existence *and* uniqueness of a
transporting next multiplier. -/
theorem feedbackTransport_existsUnique_iff {a v h uNext eNext q : ℤ}
    (hqu : q = h * uNext) (hq0 : q ≠ 0) :
    q ∣ a * v - h * eNext ↔
      ∃! aNext : ℤ, h * ((aNext - 1) * uNext + eNext) = a * v := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + 1, ?_, ?_⟩
    · calc h * (((k + 1) - 1) * uNext + eNext) = k * (h * uNext) + h * eNext := by ring
        _ = k * q + h * eNext := by rw [← hqu]
        _ = a * v := by linarith [hk]
    · intro y hy
      have hyq : (y - 1) * q = k * q := by
        calc (y - 1) * q = h * ((y - 1) * uNext + eNext) - h * eNext := by rw [hqu]; ring
          _ = a * v - h * eNext := by rw [hy]
          _ = q * k := hk
          _ = k * q := by ring
      have : y - 1 = k := mul_right_cancel₀ hq0 hyq
      linarith
  · rintro ⟨aNext, htransport, -⟩
    refine ⟨aNext - 1, ?_⟩
    calc a * v - h * eNext = h * ((aNext - 1) * uNext + eNext) - h * eNext := by
          rw [htransport]
      _ = q * (aNext - 1) := by rw [hqu]; ring

/-- **The canonical root.**  For a primitive state the *old denominator* is the
distinguished square root: its norm congruence is equivalent to existence and
uniqueness of the transporting next multiplier.  No other root of the
congruence carries that content. -/
theorem canonicalRoot_feedback_iff_existsUnique {a u v e q h uNext eNext : ℤ}
    (hprimitive : Int.gcd u v = 1)
    (he : e = v - (a - 1) * u) (hq : q = a * u - v)
    (hqu : q = h * uNext) (hq0 : q ≠ 0) :
    q ∣ v ^ 2 - h * e * eNext ↔
      ∃! aNext : ℤ, h * ((aNext - 1) * uNext + eNext) = a * v := by
  have hcop : Int.gcd e q = 1 := by rw [centered_rawNext_gcd he hq, hprimitive]
  have horient : q ∣ v - a * e := ⟨a - 1, by rw [he, hq]; ring⟩
  exact (orientedSquareRoot_iff_feedback hcop horient).trans
    (feedbackTransport_existsUnique_iff hqu hq0)

/-! ## The old denominator also carries the exact cancellation content -/

/-- **Content symmetry.**  The cancellation factor of a reduced step is
`gcd(q, v²)`, matching the known `gcd(q, a²)`.  So the old denominator is
simultaneously the canonical root and the exact carrier of the content that
must be removed. -/
theorem rawNext_gcd_eq_gcd_denominator_sq {a u v q : ℕ}
    (hcop : Nat.Coprime u v) (hq : q + v = a * u) :
    Nat.gcd q (a * v) = Nat.gcd q (v ^ 2) := by
  have hqu : Nat.Coprime q u := (rawNext_coprime_currentNumerator hcop hq).symm
  have hkey : q * v + v ^ 2 = a * u * v := by
    have : (q + v) * v = a * u * v := by rw [hq]
    nlinarith [this]
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left q (a * v))
    have hdq : Nat.gcd q (a * v) ∣ q := Nat.gcd_dvd_left q (a * v)
    have hdav : Nat.gcd q (a * v) ∣ a * v := Nat.gcd_dvd_right q (a * v)
    have hd1 : Nat.gcd q (a * v) ∣ q * v := Dvd.dvd.mul_right hdq v
    have hd2 : Nat.gcd q (a * v) ∣ a * u * v := by
      have : a * u * v = a * v * u := by ring
      rw [this]
      exact Dvd.dvd.mul_right hdav u
    have := Nat.dvd_sub hd2 hd1
    rwa [show a * u * v - q * v = v ^ 2 by omega] at this
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left q (v ^ 2))
    have hdq : Nat.gcd q (v ^ 2) ∣ q := Nat.gcd_dvd_left q (v ^ 2)
    have hdv2 : Nat.gcd q (v ^ 2) ∣ v ^ 2 := Nat.gcd_dvd_right q (v ^ 2)
    have hd1 : Nat.gcd q (v ^ 2) ∣ q * v := Dvd.dvd.mul_right hdq v
    have hduv : Nat.gcd q (v ^ 2) ∣ a * v * u := by
      have heq : a * v * u = q * v + v ^ 2 := by rw [hkey]; ring
      rw [heq]
      exact Nat.dvd_add hd1 hdv2
    have hcopd : Nat.Coprime (Nat.gcd q (v ^ 2)) u :=
      Nat.Coprime.coprime_dvd_left hdq hqu
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcopd hduv)

/-! ## The smallest artificial root -/

/-- `4` is a square root of `1` modulo `15` — and it is artificial: the
orientation `a·t ≡ -1` fails.  Deleting `horient` from
`orientedSquareRoot_iff_feedback` therefore produces a false statement. -/
theorem fifteen_fake_root_four :
    (15 : ℤ) ∣ 4 ^ 2 - 1 ∧ ¬ (15 : ℤ) ∣ 16 * 4 + 1 := by
  constructor
  · decide
  · decide

/-- The canonical root `-1` of the same congruence *is* oriented. -/
theorem fifteen_true_root_neg_one :
    (15 : ℤ) ∣ (-1 : ℤ) ^ 2 - 1 ∧ (15 : ℤ) ∣ 16 * (-1) + 1 := by
  constructor
  · decide
  · decide

/-- Orientation pins the root to a single residue class: the `2^r` solutions of
the norm congruence collapse to one realizable root. -/
theorem orientation_determines_root {a e q t t' : ℤ}
    (h1 : q ∣ t - a * e) (h2 : q ∣ t' - a * e) : q ∣ t - t' := by
  have := Dvd.dvd.sub h1 h2
  simpa using this

end ErdosProblems.Erdos243
