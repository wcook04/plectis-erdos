import ErdosProblems.Erdos243.FeedbackRealizability

/-!
# Erdős #243: cumulative-LCM height

Global coordinates which retain digit-overlap payments that can disappear
from the dynamically reduced numerator-denominator pair.
-/

namespace ErdosProblems.Erdos243

/-- Cumulative least common multiple of the initial denominator and all
digits strictly before `n`. -/
def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)

@[simp]
theorem cumulativeDigitLcm_zero (q : ℕ) (a : ℕ → ℕ) :
    cumulativeDigitLcm q a 0 = q := rfl

@[simp]
theorem cumulativeDigitLcm_succ (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeDigitLcm q a (n + 1) =
      Nat.lcm (cumulativeDigitLcm q a n) (a n) := rfl

/-- Product-cleared denominator scale through the first `n` digits. -/
def digitProductScale (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => a n * digitProductScale q a n

/-- Cumulative product of the irreversible LCM-overlap payments. -/
def cumulativeOverlapDebt (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      cumulativeOverlapDebt q a n *
        Nat.gcd (cumulativeDigitLcm q a n) (a n)

/-- Global overlap is relocation rather than erasure: at every finite
horizon, overlap debt times the cumulative LCM is exactly the full
product-cleared digit scale. -/
theorem cumulativeOverlapDebt_mul_lcm_eq_productScale
    (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeOverlapDebt q a n * cumulativeDigitLcm q a n =
      digitProductScale q a n := by
  induction n with
  | zero =>
      simp [cumulativeOverlapDebt, cumulativeDigitLcm, digitProductScale]
  | succ n ih =>
      simp only [cumulativeOverlapDebt, cumulativeDigitLcm, digitProductScale]
      calc
        (cumulativeOverlapDebt q a n *
              Nat.gcd (cumulativeDigitLcm q a n) (a n)) *
            Nat.lcm (cumulativeDigitLcm q a n) (a n) =
          cumulativeOverlapDebt q a n *
            (Nat.gcd (cumulativeDigitLcm q a n) (a n) *
              Nat.lcm (cumulativeDigitLcm q a n) (a n)) := by ring
        _ = cumulativeOverlapDebt q a n *
              (cumulativeDigitLcm q a n * a n) := by
            rw [Nat.gcd_mul_lcm]
        _ = (cumulativeOverlapDebt q a n *
              cumulativeDigitLcm q a n) * a n := by ring
        _ = digitProductScale q a n * a n := by rw [ih]
        _ = a n * digitProductScale q a n := by ring

/-- Centered remainder in cumulative-LCM coordinates. -/
def globalCentered (Λ Y b : ℕ) : ℤ :=
  (Λ : ℤ) - (b : ℤ) * Y

/-- The lifted raw numerator identity is equivalent to the pseudo-Euclidean
update once `F = Λ-bY` and `a=b+1`. -/
theorem globalLcm_numerator_update
    {Λ Y b a ρ YNext : ℕ} {F : ℤ}
    (hF : F = globalCentered Λ Y b)
    (ha : a = b + 1)
    (hraw :
      (ρ * YNext : ℤ) = (a : ℤ) * Y - Λ) :
    (ρ * YNext : ℤ) = (Y : ℤ) - F := by
  rw [hF, globalCentered, ha] at *
  push_cast at hraw ⊢
  linarith

/-- A common product-cleared scale factors out of the global numerator and
cumulative denominator exactly. -/
theorem globalContent_gcd_split (M Y Λ : ℕ) :
    Nat.gcd (M * Y) (M * Λ) = M * Nat.gcd Y Λ := by
  exact Nat.gcd_mul_left M Y Λ

/-- Exact global/local split of a reduced cancellation payment.  The factor
`ρ` is deposited in the irreversible overlap scale `M`; the remaining change
is the local lifted content. -/
theorem reducedCancellation_split_global_local
    {G GNext M MNext g gNext h ρ : ℕ}
    (hMpos : 0 < M)
    (hG : G = M * g)
    (hGNext : GNext = MNext * gNext)
    (hMNext : MNext = ρ * M)
    (hpayment : h * G = GNext) :
    h * g = ρ * gNext := by
  apply Nat.mul_left_cancel hMpos
  calc
    M * (h * g) = h * (M * g) := by ring
    _ = h * G := by rw [hG]
    _ = GNext := hpayment
    _ = MNext * gNext := hGNext
    _ = M * (ρ * gNext) := by rw [hMNext]; ring

/-- Division-free one-step amortization: if negative centered mass is at
most `1/K` of the lifted numerator, then overlap payment plus next height is
bounded by the corresponding near-unit factor. -/
theorem globalNegativeMass_step_bound
    {K ρ Y YNext : ℕ} {F : ℤ}
    (hupdate : (ρ * YNext : ℤ) = (Y : ℤ) - F)
    (hsmall : (K : ℤ) * (-F) ≤ Y) :
    (K : ℤ) * (ρ * YNext) ≤ (K + 1 : ℤ) * Y := by
  nlinarith

/-- Positive global centered error strictly decreases lifted height after
charging the overlap payment. -/
theorem globalPositiveCentered_strict_payment_descent
    {ρ Y YNext : ℕ} {F : ℤ}
    (hupdate : (ρ * YNext : ℤ) = (Y : ℤ) - F)
    (hF : 0 < F) :
    (ρ * YNext : ℤ) < Y := by
  linarith

/-- Exact returned-error telescope.  It is an identity over `ℚ`; obtaining
well-founded descent still requires arithmetic height information. -/
theorem returnedError_step
    {x xNext a b bNext Δ z zNext : ℚ}
    (ha0 : a ≠ 0)
    (hb0 : b ≠ 0)
    (hbNext0 : bNext ≠ 0)
    (hxNext : xNext = x - 1 / a)
    (ha : a = b + 1)
    (hbNext : bNext = a * b + Δ)
    (hz : z = x - 1 / b)
    (hzNext : zNext = xNext - 1 / bNext) :
    zNext = z + Δ / (a * b * bNext) := by
  have hscalar :
      1 / b - 1 / a - 1 / bNext =
        Δ / (a * b * bNext) := by
    field_simp [ha0, hb0, hbNext0]
    calc
      (a - b) * bNext - b * a = bNext - b * a := by rw [ha]; ring
      _ = Δ := by rw [hbNext]; ring
  calc
    zNext = x - 1 / a - 1 / bNext := by rw [hzNext, hxNext]
    _ = (x - 1 / b) + (1 / b - 1 / a - 1 / bNext) := by ring
    _ = z + Δ / (a * b * bNext) := by rw [← hz, hscalar]

end ErdosProblems.Erdos243
