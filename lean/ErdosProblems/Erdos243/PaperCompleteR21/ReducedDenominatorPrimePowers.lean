import ErdosProblems.Erdos243.RecordIncrementBarrier
import ErdosProblems.Erdos243.PaperCompleteR11.CanonicalGrowthBounds
import ErdosProblems.Erdos243.PaperCompleteR11.QuantitativeRecordDichotomy
import ErdosProblems.Erdos243.PaperCompleteR7.QuantitativeTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős 243: the standing hypotheses of the reduced-numerator section

This file transcribes the *standing hypotheses* of
`paper/reasoning-parts/erdos243/core.tex`,
§`long243:sec:records` ("New maxima of reduced numerators"), together with the
objects that section defines, and then proves two of its environments.

The standing hypotheses are the hypotheses of Problem `long243:res:problem`
(Erdős #243): strictly increasing positive integers `a` with
`a (n+1) / a n ^ 2 → 1` whose reciprocal sum is rational.  The section's
integer tails `C`, `D`, `E` are *not* assumed: they are the canonical ones
built from the rational sum in `PaperCompleteR7.CanonicalState`, so the
normalised vanishing `|E n| / C n → 0` is a theorem here, not a hypothesis.

Over that data the section puts

* `G n = gcd (C n) (D n)`, `u n = C n / G n`, `v n = D n / G n`,
  `redErr n = E n / G n` (the paper's `ẽ n`),
* `canc n = G (n+1) / G n` (the paper's `h n`), `w n = a n * u n - v n`,
* `R n = max_{k ≤ n} u k`, `Hmax n = max_{j ≤ n} C j`,
* `negPart n = (- redErr n)₊` (the paper's `m n`),
  `amp n = R n * negPart n / u n` (the paper's `𝒜 n`),
  `delta n = (a n ^ 2 / a (n+1) - 1)₊`.

The environments proved here are

* `long243:res:oddpowersupply`, the supply of a large odd prime power in the
  reduced denominator (`StandingOrbit.oddPrimePower_supply`, with its
  natural-exponent form `StandingOrbit.oddPrimePower_supply_nat`);
* `long243:res:unitrecord`, unit record increments force the Sylvester
  recurrence, and the finiteness equivalence
  (`StandingOrbit.unitRecordIncrement_sylvesterNext`,
  `StandingOrbit.unitRecordIncrement_criterion`).

The proof of the prime-power supply follows the paper: `v n ∣ lcm (q, a 0, …,
a (n-1))` bounds the two-primary part of `v n` by `a (n-1)`, while
`u n / v n ≤ 2 / a n` bounds `v n` from below by `a n / 2`; the odd part of
`v n` is therefore at least `a (n-1) / 4`, which is doubly exponential, and a
number all of whose exact odd prime-power factors are at most `B` is at most
`B ^ (B+1)`, which is only `exp(o(n))` because `log (Hmax n) = o(n)`.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR11
open scoped BigOperators Topology

/-! ## 1. The standing hypotheses -/

/-- **The standing hypotheses of §`long243:sec:records`.**

These are exactly the hypotheses of Problem `long243:res:problem`: a strictly
increasing sequence of positive integers with `a (n+1) / a n ^ 2 → 1` and
rational reciprocal sum, presented by an explicit integer numerator `num` and
positive natural denominator `den`.

The section's integer tails are the canonical ones constructed from this data;
they are definitions below, not further hypotheses. -/
structure StandingOrbit where
  /-- The multiplier sequence `a n`. -/
  a : ℕ → ℕ
  /-- The numerator of the rational reciprocal sum. -/
  num : ℤ
  /-- The denominator of the rational reciprocal sum. -/
  den : ℕ
  /-- `1 ≤ a 1 < a 2 < ⋯`. -/
  a_strictMono : StrictMono a
  /-- Positivity of the multipliers. -/
  a_pos : ∀ n, 0 < a n
  /-- Positivity of the denominator of the sum. -/
  den_pos : 0 < den
  /-- `∑ 1 / a n = num / den ∈ ℚ`. -/
  hasSum : HasSum (fun n ↦ 1 / (a n : ℝ)) ((num : ℝ) / (den : ℝ))
  /-- `a (n+1) / a n ^ 2 → 1`. -/
  growth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)

namespace StandingOrbit

variable (O : StandingOrbit)

/-! ### The objects of the section -/

/-- `C n`: the cleared integer numerator of the reciprocal tail. -/
def C : ℕ → ℕ := canonicalNaturalNumerator O.a O.num O.den

/-- `D n = q a 0 ⋯ a (n-1)`: the cleared denominator. -/
def D : ℕ → ℕ := canonicalDenominator O.a O.den

/-- `E n = D n - (a n - 1) C n`, the deviation from a Sylvester tail. -/
def Err (n : ℕ) : ℤ := (O.D n : ℤ) - ((O.a n : ℤ) - 1) * (O.C n : ℤ)

/-- `G n = gcd (C n) (D n)`. -/
def G (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)

/-- `u n = C n / G n`: the reduced numerator. -/
def u (n : ℕ) : ℕ := O.C n / O.G n

/-- `v n = D n / G n`: the reduced denominator. -/
def v (n : ℕ) : ℕ := O.D n / O.G n

/-- `ẽ n = E n / G n`: the reduced signed error. -/
def redErr (n : ℕ) : ℤ := (O.v n : ℤ) - ((O.a n : ℤ) - 1) * (O.u n : ℤ)

/-- `h n = G (n+1) / G n`: the cancellation factor. -/
def canc (n : ℕ) : ℕ := O.G (n + 1) / O.G n

/-- `w n = a n * u n - v n`: the raw next numerator, before reduction. -/
def w (n : ℕ) : ℕ := O.a n * O.u n - O.v n

/-- `R n = max_{k ≤ n} u k`. -/
def R : ℕ → ℕ := runningMax O.u

/-- `H n = max_{j ≤ n} C j`. -/
def Hmax : ℕ → ℕ := runningMax O.C

/-- `m n = (- ẽ n)₊`. -/
def negPart (n : ℕ) : ℕ := (-O.redErr n).toNat

/-- `𝒜 n = (R n / u n) * m n`. -/
noncomputable def amp (n : ℕ) : ℝ := (O.R n : ℝ) * (O.negPart n : ℝ) / (O.u n : ℝ)

/-- `δ n = (a n ^ 2 / a (n+1) - 1)₊`. -/
noncomputable def delta (n : ℕ) : ℝ :=
  max 0 ((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)

/-! ### Basic properties of the canonical tail -/

theorem tailData :
    (∀ n, 0 < O.C n) ∧ (∀ n, 0 < O.D n) ∧
    (∀ n, O.C (n + 1) + O.D n = O.a n * O.C n) ∧
    (∀ n, O.D (n + 1) = O.a n * O.D n) ∧
    (∀ n, (O.C n : ℝ) = (O.D n : ℝ) * realTail (fun k ↦ 1 / (O.a k : ℝ)) n) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    canonical_integer_tail O.a O.a_pos O.num O.den O.den_pos O.hasSum
  exact ⟨h1, h2, h3, h4, h5⟩

theorem C_pos (n : ℕ) : 0 < O.C n := O.tailData.1 n

theorem D_pos (n : ℕ) : 0 < O.D n := O.tailData.2.1 n

theorem C_step (n : ℕ) : O.C (n + 1) + O.D n = O.a n * O.C n := O.tailData.2.2.1 n

theorem D_step (n : ℕ) : O.D (n + 1) = O.a n * O.D n := O.tailData.2.2.2.1 n

theorem C_repr (n : ℕ) :
    (O.C n : ℝ) = (O.D n : ℝ) * realTail (fun k ↦ 1 / (O.a k : ℝ)) n :=
  O.tailData.2.2.2.2 n

theorem vanishing (K : ℕ) : ∃ N, ∀ n, N ≤ n → K * (O.Err n).natAbs < O.C n := by
  obtain ⟨_, _, _, _, _, hv, _⟩ :=
    canonical_integer_tail_normalized O.a O.a_strictMono O.a_pos O.num O.den
      O.den_pos O.hasSum O.growth
  exact hv K

/-! ### The reduced data -/

theorem G_pos (n : ℕ) : 0 < O.G n := by
  rcases Nat.eq_zero_or_pos (O.G n) with h | h
  · rw [G, Nat.gcd_eq_zero_iff] at h
    exact absurd h.1 (O.C_pos n).ne'
  · exact h

theorem G_dvd_C (n : ℕ) : O.G n ∣ O.C n := Nat.gcd_dvd_left _ _

theorem G_dvd_D (n : ℕ) : O.G n ∣ O.D n := Nat.gcd_dvd_right _ _

theorem u_mul (n : ℕ) : O.u n * O.G n = O.C n := Nat.div_mul_cancel (O.G_dvd_C n)

theorem v_mul (n : ℕ) : O.v n * O.G n = O.D n := Nat.div_mul_cancel (O.G_dvd_D n)

theorem u_pos (n : ℕ) : 0 < O.u n := by
  have h := O.u_mul n
  have := O.C_pos n
  rcases Nat.eq_zero_or_pos (O.u n) with h0 | h0
  · rw [h0, Nat.zero_mul] at h; omega
  · exact h0

theorem v_pos (n : ℕ) : 0 < O.v n := by
  have h := O.v_mul n
  have := O.D_pos n
  rcases Nat.eq_zero_or_pos (O.v n) with h0 | h0
  · rw [h0, Nat.zero_mul] at h; omega
  · exact h0

theorem coprime_u_v (n : ℕ) : Nat.Coprime (O.u n) (O.v n) :=
  Nat.coprime_div_gcd_div_gcd (O.G_pos n)

theorem u_le_C (n : ℕ) : O.u n ≤ O.C n := Nat.div_le_self _ _

theorem G_dvd_G_succ (n : ℕ) : O.G n ∣ O.G (n + 1) := by
  refine Nat.dvd_gcd ?_ ?_
  · have hsum : O.G n ∣ O.C (n + 1) + O.D n := by
      rw [O.C_step n]
      exact Dvd.dvd.mul_left (O.G_dvd_C n) _
    exact (Nat.dvd_add_iff_left (O.G_dvd_D n)).mpr hsum
  · rw [O.D_step n]
    exact Dvd.dvd.mul_left (O.G_dvd_D n) _

theorem canc_mul (n : ℕ) : O.canc n * O.G n = O.G (n + 1) :=
  Nat.div_mul_cancel (O.G_dvd_G_succ n)

theorem v_le (n : ℕ) : O.v n ≤ O.a n * O.u n := by
  have hG := O.G_pos n
  have h1 : O.v n * O.G n ≤ (O.a n * O.u n) * O.G n := by
    rw [O.v_mul n, Nat.mul_assoc, O.u_mul n]
    have := O.C_step n
    omega
  exact Nat.le_of_mul_le_mul_right h1 hG

theorem w_add_v (n : ℕ) : O.w n + O.v n = O.a n * O.u n :=
  Nat.sub_add_cancel (O.v_le n)

theorem w_mul_G (n : ℕ) : O.w n * O.G n = O.C (n + 1) := by
  have h1 : (O.w n + O.v n) * O.G n = (O.a n * O.u n) * O.G n := by rw [O.w_add_v n]
  rw [Nat.add_mul, O.v_mul n, Nat.mul_assoc, O.u_mul n] at h1
  have := O.C_step n
  omega

theorem w_pos (n : ℕ) : 0 < O.w n := by
  have h := O.w_mul_G n
  have := O.C_pos (n + 1)
  rcases Nat.eq_zero_or_pos (O.w n) with h0 | h0
  · rw [h0, Nat.zero_mul] at h; omega
  · exact h0

theorem num_step (n : ℕ) : O.w n = O.canc n * O.u (n + 1) := by
  have hG := O.G_pos n
  refine Nat.eq_of_mul_eq_mul_right hG ?_
  have h2 : (O.canc n * O.u (n + 1)) * O.G n = O.C (n + 1) := by
    calc (O.canc n * O.u (n + 1)) * O.G n = O.u (n + 1) * (O.canc n * O.G n) := by ring
    _ = O.u (n + 1) * O.G (n + 1) := by rw [O.canc_mul n]
    _ = O.C (n + 1) := O.u_mul (n + 1)
  rw [O.w_mul_G n, h2]

theorem den_step (n : ℕ) : O.a n * O.v n = O.canc n * O.v (n + 1) := by
  have hG := O.G_pos n
  refine Nat.eq_of_mul_eq_mul_right hG ?_
  have hl : (O.a n * O.v n) * O.G n = O.D (n + 1) := by
    calc (O.a n * O.v n) * O.G n = O.a n * (O.v n * O.G n) := by ring
    _ = O.a n * O.D n := by rw [O.v_mul n]
    _ = O.D (n + 1) := (O.D_step n).symm
  have hr : (O.canc n * O.v (n + 1)) * O.G n = O.D (n + 1) := by
    calc (O.canc n * O.v (n + 1)) * O.G n = O.v (n + 1) * (O.canc n * O.G n) := by ring
    _ = O.v (n + 1) * O.G (n + 1) := by rw [O.canc_mul n]
    _ = O.D (n + 1) := O.v_mul (n + 1)
  rw [hl, hr]

theorem redErr_mul (n : ℕ) : (O.G n : ℤ) * O.redErr n = O.Err n := by
  have hu : ((O.u n : ℤ)) * (O.G n : ℤ) = (O.C n : ℤ) := by exact_mod_cast O.u_mul n
  have hv : ((O.v n : ℤ)) * (O.G n : ℤ) = (O.D n : ℤ) := by exact_mod_cast O.v_mul n
  rw [redErr, Err, ← hu, ← hv]
  ring

/-- The reduced normalised error vanishes: the division-free form of
`|ẽ n| / u n → 0`. -/
theorem redErr_vanishing (K : ℕ) : ∃ N, ∀ n, N ≤ n → K * (O.redErr n).natAbs < O.u n := by
  obtain ⟨N, hN⟩ := O.vanishing K
  refine ⟨N, fun n hn ↦ ?_⟩
  have hG := O.G_pos n
  have h := hN n hn
  have habs : (O.Err n).natAbs = O.G n * (O.redErr n).natAbs := by
    rw [← O.redErr_mul n, Int.natAbs_mul, Int.natAbs_natCast]
  rw [habs, ← O.u_mul n] at h
  have h' : O.G n * (K * (O.redErr n).natAbs) < O.G n * O.u n := by
    calc O.G n * (K * (O.redErr n).natAbs) = K * (O.G n * (O.redErr n).natAbs) := by ring
    _ < O.u n * O.G n := h
    _ = O.G n * O.u n := by ring
  exact Nat.lt_of_mul_lt_mul_left h'

/-- The paper's `e n = v n - (a n - 1) u n`, in the shape used by
`recordIncrementOne_sylvesterNext_eventually`. -/
theorem redErr_eq (n : ℕ) :
    O.redErr n = (O.v n : ℤ) - ((O.a n : ℤ) - 1) * (O.u n : ℤ) := rfl

theorem canc_pos (n : ℕ) : 0 < O.canc n := by
  have h := O.canc_mul n
  have := O.G_pos (n + 1)
  rcases Nat.eq_zero_or_pos (O.canc n) with h0 | h0
  · rw [h0, Nat.zero_mul] at h; omega
  · exact h0

/-- The paper's `w n = u n - ẽ n`. -/
theorem w_eq_sub_redErr (n : ℕ) : (O.w n : ℤ) = (O.u n : ℤ) - O.redErr n := by
  have h : ((O.w n + O.v n : ℕ) : ℤ) = ((O.a n * O.u n : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun t : ℕ ↦ (t : ℤ)) (O.w_add_v n)
  push_cast at h
  rw [redErr]
  linarith

theorem w_le (n : ℕ) : O.w n ≤ O.u n + O.negPart n := by
  have h := O.w_eq_sub_redErr n
  have hm : -(O.redErr n) ≤ (O.negPart n : ℤ) := Int.self_le_toNat _
  have hz : (O.w n : ℤ) ≤ ((O.u n + O.negPart n : ℕ) : ℤ) := by push_cast; omega
  exact_mod_cast hz

/-- The paper's `u (n+1) ≤ u n + m n`: the reduced numerator rises by at most
the negative part of the reduced error. -/
theorem u_succ_le (n : ℕ) : O.u (n + 1) ≤ O.u n + O.negPart n := by
  have h1 : O.u (n + 1) ≤ O.w n := by
    rw [O.num_step n]
    exact Nat.le_mul_of_pos_left _ (O.canc_pos n)
  exact le_trans h1 (O.w_le n)

/-- The paper's `m n ≤ 𝒜 n`, because `R n ≥ u n`. -/
theorem negPart_le_amp (n : ℕ) : (O.negPart n : ℝ) ≤ O.amp n := by
  have hu : (0 : ℝ) < (O.u n : ℝ) := by exact_mod_cast O.u_pos n
  have hR : (O.u n : ℝ) ≤ (O.R n : ℝ) := by
    exact_mod_cast le_runningMax O.u (le_refl n)
  have hm : (0 : ℝ) ≤ (O.negPart n : ℝ) := Nat.cast_nonneg _
  rw [amp, le_div_iff₀ hu]
  nlinarith

end StandingOrbit

/-! ## 2. The reduced denominator divides an LCM of the data -/

/-- `L n = lcm (q, a 0, …, a (n-1))`. -/
def lcmUpTo (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (lcmUpTo q a n) (a n)

theorem den_dvd_lcmUpTo (q : ℕ) (a : ℕ → ℕ) : ∀ n, q ∣ lcmUpTo q a n
  | 0 => dvd_rfl
  | n + 1 => (den_dvd_lcmUpTo q a n).trans (Nat.dvd_lcm_left _ _)

theorem term_dvd_lcmUpTo (q : ℕ) (a : ℕ → ℕ) :
    ∀ n j, j < n → a j ∣ lcmUpTo q a n := by
  intro n
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
      intro j hj
      rcases Nat.lt_or_ge j n with h | h
      · exact (ih j h).trans (Nat.dvd_lcm_left _ _)
      · have : j = n := by omega
        subst this
        exact Nat.dvd_lcm_right _ _

theorem lcmUpTo_pos {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n) :
    ∀ n, 0 < lcmUpTo q a n := by
  intro n
  induction n with
  | zero => exact hq
  | succ n ih =>
      have : Nat.lcm (lcmUpTo q a n) (a n) ≠ 0 := Nat.lcm_ne_zero ih.ne' (ha n).ne'
      exact Nat.pos_of_ne_zero this

namespace StandingOrbit

variable (O : StandingOrbit)

theorem C_cast (n : ℕ) :
    (O.C n : ℤ) = clearedIntegerNumerator O.a O.num O.den n := by
  have hpos := O.C_pos n
  have h : 0 ≤ clearedIntegerNumerator O.a O.num O.den n := by
    by_contra hc
    push_neg at hc
    have hz : (clearedIntegerNumerator O.a O.num O.den n).toNat = 0 :=
      Int.toNat_eq_zero.mpr hc.le
    have : O.C n = 0 := hz
    omega
  show ((clearedIntegerNumerator O.a O.num O.den n).toNat : ℤ) = _
  exact Int.toNat_of_nonneg h

theorem D_dvd_lcm_mul_C (n : ℕ) :
    O.D n ∣ lcmUpTo O.den O.a n * O.C n := by
  have key : ((O.D n : ℕ) : ℤ) ∣ ((lcmUpTo O.den O.a n : ℕ) : ℤ) * ((O.C n : ℕ) : ℤ) := by
    rw [O.C_cast n]
    have hD : ((O.D n : ℕ) : ℤ) = (O.den : ℤ) * (prefixProduct O.a n : ℤ) := by
      simp only [D, canonicalDenominator]
      push_cast
      ring
    rw [hD, clearedIntegerNumerator, mul_sub, Finset.mul_sum]
    refine dvd_sub ?_ (Finset.dvd_sum ?_)
    · obtain ⟨s, hs⟩ := den_dvd_lcmUpTo O.den O.a n
      refine ⟨(s : ℤ) * O.num, ?_⟩
      have : ((lcmUpTo O.den O.a n : ℕ) : ℤ) = (O.den : ℤ) * (s : ℤ) := by
        exact_mod_cast congrArg (fun t : ℕ ↦ (t : ℤ)) hs
      rw [this]
      ring
    · intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      obtain ⟨t, ht⟩ := term_dvd_lcmUpTo O.den O.a n j hjn
      have hdvd : O.a j ∣ prefixProduct O.a n := Finset.dvd_prod_of_mem O.a hj
      obtain ⟨r, hr⟩ := hdvd
      have hquot : prefixProduct O.a n / O.a j = r := by
        rw [hr]
        exact Nat.mul_div_cancel_left r (O.a_pos j)
      refine ⟨(t : ℤ), ?_⟩
      rw [hquot]
      have hL : ((lcmUpTo O.den O.a n : ℕ) : ℤ) = (O.a j : ℤ) * (t : ℤ) := by
        exact_mod_cast congrArg (fun x : ℕ ↦ (x : ℤ)) ht
      have hP : ((prefixProduct O.a n : ℕ) : ℤ) = (O.a j : ℤ) * (r : ℤ) := by
        exact_mod_cast congrArg (fun x : ℕ ↦ (x : ℤ)) hr
      rw [hL, hP]
      ring
  exact_mod_cast key

theorem v_dvd_lcmUpTo (n : ℕ) : O.v n ∣ lcmUpTo O.den O.a n := by
  have hG := O.G_pos n
  have h := O.D_dvd_lcm_mul_C n
  rw [← O.v_mul n, ← O.u_mul n] at h
  have h2 : O.v n * O.G n ∣ (lcmUpTo O.den O.a n * O.u n) * O.G n := by
    rw [Nat.mul_assoc]
    exact h
  have h3 : O.v n ∣ lcmUpTo O.den O.a n * O.u n :=
    (Nat.mul_dvd_mul_iff_right hG).mp h2
  exact (O.coprime_u_v n).symm.dvd_of_dvd_mul_right h3

end StandingOrbit

/-! ## 3. The two-primary part of the LCM -/

/-- A prime power dividing an LCM divides one of the two arguments. -/
theorem primePow_dvd_lcm_cases {p k x y : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : p ^ k ∣ Nat.lcm x y) : p ^ k ∣ x ∨ p ^ k ∣ y := by
  have hlcm : Nat.lcm x y ≠ 0 := Nat.lcm_ne_zero hx hy
  rw [hp.pow_dvd_iff_le_factorization hlcm, Nat.factorization_lcm hx hy,
    Finsupp.sup_apply] at h
  rcases le_sup_iff.mp h with h' | h'
  · left
    exact (hp.pow_dvd_iff_le_factorization hx).mpr h'
  · right
    exact (hp.pow_dvd_iff_le_factorization hy).mpr h'

/-- The two-primary part of `lcm (q, a 0, …, a n)` is at most `max q (a n)`:
every `2`-power dividing it already divides `q` or one of the `a j`, `j ≤ n`,
and those are bounded by `max q (a n)` because `a` is strictly increasing. -/
theorem twoPow_dvd_lcmUpTo_le {q : ℕ} {a : ℕ → ℕ} (hq : 0 < q) (ha : ∀ n, 0 < a n)
    (hmono : StrictMono a) :
    ∀ n k : ℕ, 2 ^ k ∣ lcmUpTo q a (n + 1) → 2 ^ k ≤ max q (a n) := by
  intro n
  induction n with
  | zero =>
      intro k hk
      rcases primePow_dvd_lcm_cases Nat.prime_two hq.ne' (ha 0).ne' hk with h | h
      · exact le_trans (Nat.le_of_dvd hq h) (le_max_left _ _)
      · exact le_trans (Nat.le_of_dvd (ha 0) h) (le_max_right _ _)
  | succ n ih =>
      intro k hk
      have hL : lcmUpTo q a (n + 1) ≠ 0 := (lcmUpTo_pos hq ha (n + 1)).ne'
      rcases primePow_dvd_lcm_cases Nat.prime_two hL (ha (n + 1)).ne' hk with h | h
      · have := ih k h
        have hlt : a n < a (n + 1) := hmono (Nat.lt_succ_self n)
        omega
      · have := Nat.le_of_dvd (ha (n + 1)) h
        omega

/-! ## 4. A number whose exact odd prime powers are small is small -/

/-- If every exact prime-power factor of `W` is at most `B`, then `W ≤ B ^ (B+1)`:
the exponents are bounded by `B` and there are at most `B + 1` primes below `B`. -/
theorem le_pow_of_primePow_le {W B : ℕ} (hW : W ≠ 0) (hB : 1 ≤ B)
    (h : ∀ p ∈ W.primeFactors, p ^ (W.factorization p) ≤ B) :
    W ≤ B ^ (B + 1) := by
  have hprod : ∏ p ∈ W.primeFactors, p ^ (W.factorization p) = W := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hW
  have hcard : W.primeFactors.card ≤ B + 1 := by
    have hsub : W.primeFactors ⊆ Finset.range (B + 1) := by
      intro p hp
      have hple : p ≤ p ^ (W.factorization p) := by
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hk : 1 ≤ W.factorization p := by
          have := (Nat.mem_primeFactors.mp hp)
          rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp hW, pow_one]
          exact this.2.1
        calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (W.factorization p) := Nat.pow_le_pow_right hpp.pos hk
      have := h p hp
      exact Finset.mem_range.mpr (by omega)
    calc W.primeFactors.card ≤ (Finset.range (B + 1)).card := Finset.card_le_card hsub
    _ = B + 1 := Finset.card_range _
  calc W = ∏ p ∈ W.primeFactors, p ^ (W.factorization p) := hprod.symm
  _ ≤ B ^ W.primeFactors.card := Finset.prod_le_pow_card _ _ _ h
  _ ≤ B ^ (B + 1) := Nat.pow_le_pow_right hB hcard

/-! ## 5. Growth inputs -/

/-- The running maximum commutes with a power. -/
theorem runningMax_pow (U : ℕ → ℕ) (k : ℕ) :
    ∀ n, runningMax (fun j ↦ U j ^ k) n = (runningMax U n) ^ k := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show max (runningMax (fun j ↦ U j ^ k) n) (U (n + 1) ^ k)
        = (max (runningMax U n) (U (n + 1))) ^ k
      rw [ih]
      rcases le_total (runningMax U n) (U (n + 1)) with h | h
      · rw [max_eq_right h, max_eq_right (Nat.pow_le_pow_left h k)]
      · rw [max_eq_left h, max_eq_left (Nat.pow_le_pow_left h k)]

namespace StandingOrbit

variable (O : StandingOrbit)

/-- `Hmax n ^ k` has a geometric envelope of ratio `3/2`: this is the
formal content of `log (Hmax n) = o(n)` used in the paper. -/
theorem Hmax_pow_envelope (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ((O.Hmax n ^ k : ℕ) : ℝ) ≤ K * (3 / 2 : ℝ) ^ n := by
  have hratio : Tendsto (fun n ↦ (O.C (n + 1) : ℝ) / (O.C n : ℝ)) atTop (𝓝 1) :=
    canonical_numerator_ratio_tendsto_one O.a O.a_strictMono O.a_pos O.num O.den
      O.den_pos O.hasSum O.growth
  have hpow : Tendsto (fun n ↦ (((O.C (n + 1) ^ k : ℕ) : ℝ)) / ((O.C n ^ k : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have h := hratio.pow k
    rw [one_pow] at h
    refine h.congr (fun n ↦ ?_)
    push_cast
    rw [div_pow]
  obtain ⟨K, hK, _, hmax⟩ :=
    positive_ratio_one_geometric_envelope (fun n ↦ O.C n ^ k)
      (fun n ↦ pow_pos (O.C_pos n) k) hpow (3 / 2 : ℝ) (by norm_num)
  refine ⟨K, hK, fun n ↦ ?_⟩
  have := hmax n
  rwa [runningMax_pow O.C k n] at this

/-- `a n * (tail) ≤ 2` eventually, hence `a n ≤ 2 * v n`. -/
theorem a_le_two_mul_v : ∃ N, ∀ n, N ≤ n → O.a n ≤ 2 * O.v n := by
  have hpos : ∀ n, 0 < (1 : ℝ) / (O.a n : ℝ) := fun n ↦
    one_div_pos.mpr (by exact_mod_cast O.a_pos n)
  have hratio := reciprocal_successive_ratio_tendsto_zero O.a O.a_strictMono O.a_pos O.growth
  have hlim := realTail_div_term_tendsto_one (fun k ↦ 1 / (O.a k : ℝ))
    O.hasSum.summable hpos hratio
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim 1 (by norm_num)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hh := hN n hn
  simp only [Real.dist_eq] at hh
  have hub : realTail (fun k ↦ 1 / (O.a k : ℝ)) n / (1 / (O.a n : ℝ)) ≤ 2 := by
    have := (abs_lt.mp hh).2
    linarith
  have hap : (0 : ℝ) < (O.a n : ℝ) := by exact_mod_cast O.a_pos n
  rw [div_div_eq_mul_div, div_one] at hub
  have hkey : (O.a n : ℝ) * realTail (fun k ↦ 1 / (O.a k : ℝ)) n ≤ 2 := by
    rw [mul_comm]; exact hub
  -- `C n = D n * tail` turns this into `a n * C n ≤ 2 * D n`.
  have hDpos : (0 : ℝ) < (O.D n : ℝ) := by exact_mod_cast O.D_pos n
  have hCD : (O.a n : ℝ) * (O.C n : ℝ) ≤ 2 * (O.D n : ℝ) := by
    rw [O.C_repr n]
    have hmul := mul_le_mul_of_nonneg_left hkey hDpos.le
    nlinarith [hmul]
  have hCDn : O.a n * O.C n ≤ 2 * O.D n := by exact_mod_cast hCD
  -- divide by `G n` and use `1 ≤ u n`
  have hG := O.G_pos n
  have h1 : (O.a n * O.u n) * O.G n ≤ (2 * O.v n) * O.G n := by
    rw [Nat.mul_assoc, O.u_mul n, Nat.mul_assoc, O.v_mul n]
    exact hCDn
  have h2 : O.a n * O.u n ≤ 2 * O.v n := Nat.le_of_mul_le_mul_right h1 hG
  have h3 : 1 ≤ O.u n := O.u_pos n
  nlinarith

/-! ### The odd part of the reduced denominator -/

/-- The two-primary part `2 ^ ν₂(v n)` of the reduced denominator. -/
def twoPart (n : ℕ) : ℕ := 2 ^ ((O.v n).factorization 2)

/-- The odd part `W n` of the reduced denominator. -/
def oddPart (n : ℕ) : ℕ := O.v n / O.twoPart n

theorem twoPart_dvd (n : ℕ) : O.twoPart n ∣ O.v n :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (O.v_pos n).ne').mpr le_rfl

theorem twoPart_mul_oddPart (n : ℕ) : O.twoPart n * O.oddPart n = O.v n :=
  Nat.mul_div_cancel' (O.twoPart_dvd n)

theorem oddPart_dvd (n : ℕ) : O.oddPart n ∣ O.v n :=
  ⟨O.twoPart n, by rw [← O.twoPart_mul_oddPart n]; ring⟩

theorem oddPart_pos (n : ℕ) : 0 < O.oddPart n := by
  have h := O.twoPart_mul_oddPart n
  have hv := O.v_pos n
  rcases Nat.eq_zero_or_pos (O.oddPart n) with h0 | h0
  · rw [h0, Nat.mul_zero] at h; omega
  · exact h0

theorem twoPow_succ_dvd {s x c : ℕ} (h : 2 ^ s * (2 * c) = x) : 2 ^ (s + 1) ∣ x :=
  ⟨c, by rw [← h]; ring⟩

theorem two_not_dvd_oddPart (n : ℕ) : ¬ (2 ∣ O.oddPart n) := by
  intro h
  obtain ⟨c, hc⟩ := h
  have hmul := O.twoPart_mul_oddPart n
  rw [hc] at hmul
  have hmul' : (2 : ℕ) ^ ((O.v n).factorization 2) * (2 * c) = O.v n := hmul
  have hdvd : (2 : ℕ) ^ ((O.v n).factorization 2 + 1) ∣ O.v n := twoPow_succ_dvd hmul'
  have h2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (O.v_pos n).ne').mp hdvd
  omega

/-- The odd part of the reduced denominator is at least `a (n-1) / 4`.
This is the paper's `W n ≥ a (n-1) / 4`: the reduced denominator is at least
`a n / 2`, its two-primary part is at most `a (n-1)`, and `a (n-1) ^ 2 ≤ 2 a n`. -/
theorem oddPart_lower : ∃ N, ∀ n, N ≤ n → O.a n ≤ 4 * O.oddPart (n + 1) := by
  obtain ⟨N₁, hN₁⟩ := O.a_le_two_mul_v
  obtain ⟨N₂, hN₂⟩ := quadratic_brackets_of_limit O.a O.a_pos O.growth
  refine ⟨max (max N₁ N₂) O.den, fun n hn ↦ ?_⟩
  have hq : O.den ≤ O.a n := by
    have h := strictMono_nat_linear_lower O.a O.a_strictMono n
    have : O.den ≤ n := le_trans (le_max_right _ _) hn
    omega
  have hv : O.a (n + 1) ≤ 2 * O.v (n + 1) := hN₁ (n + 1) (by omega)
  have hbr := (hN₂ n (by omega)).1
  have hTW := O.twoPart_mul_oddPart (n + 1)
  have hTdvd : (2 : ℕ) ^ ((O.v (n + 1)).factorization 2) ∣ lcmUpTo O.den O.a (n + 1) :=
    dvd_trans (O.twoPart_dvd (n + 1)) (O.v_dvd_lcmUpTo (n + 1))
  have hT : O.twoPart (n + 1) ≤ O.a n := by
    have h :=
      twoPow_dvd_lcmUpTo_le O.den_pos O.a_pos O.a_strictMono n
        ((O.v (n + 1)).factorization 2) hTdvd
    have : max O.den (O.a n) = O.a n := max_eq_right hq
    rw [this] at h
    exact h
  have h1 : O.v (n + 1) ≤ O.a n * O.oddPart (n + 1) := by
    rw [← hTW]
    exact Nat.mul_le_mul hT (le_refl _)
  have hstep : O.a n * O.a n ≤ O.a n * (4 * O.oddPart (n + 1)) := by
    calc O.a n * O.a n = O.a n ^ 2 := by ring
    _ ≤ 2 * O.a (n + 1) := hbr
    _ ≤ 2 * (2 * O.v (n + 1)) := Nat.mul_le_mul (le_refl 2) hv
    _ = 4 * O.v (n + 1) := by ring
    _ ≤ 4 * (O.a n * O.oddPart (n + 1)) := Nat.mul_le_mul (le_refl 4) h1
    _ = O.a n * (4 * O.oddPart (n + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left hstep (O.a_pos n)

/-! ### The subexponential envelope of the running maximum -/

theorem one_le_Hmax (n : ℕ) : 1 ≤ O.Hmax n :=
  le_trans (O.C_pos 0) (le_runningMax O.C (Nat.zero_le n))

theorem Hmax_pow_two_le (A : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
    ((((O.Hmax n + 2) ^ A : ℕ) : ℝ)) ^ 2 ≤ K * (3 / 2 : ℝ) ^ n := by
  obtain ⟨K, hK, hKenv⟩ := O.Hmax_pow_envelope (2 * A)
  refine ⟨3 ^ (2 * A) * K, by positivity, fun n ↦ ?_⟩
  have hle : (O.Hmax n + 2) ^ (2 * A) ≤ 3 ^ (2 * A) * O.Hmax n ^ (2 * A) := by
    rw [← Nat.mul_pow]
    refine Nat.pow_le_pow_left ?_ _
    have := O.one_le_Hmax n
    omega
  calc ((((O.Hmax n + 2) ^ A : ℕ) : ℝ)) ^ 2
      = (((O.Hmax n + 2) ^ (2 * A) : ℕ) : ℝ) := by push_cast; ring
  _ ≤ ((3 ^ (2 * A) * O.Hmax n ^ (2 * A) : ℕ) : ℝ) := by exact_mod_cast hle
  _ = (3 : ℝ) ^ (2 * A) * ((O.Hmax n ^ (2 * A) : ℕ) : ℝ) := by push_cast; ring
  _ ≤ (3 : ℝ) ^ (2 * A) * (K * (3 / 2 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (hKenv n) (by positivity)
  _ = (3 ^ (2 * A) * K) * (3 / 2 : ℝ) ^ n := by ring

/-- The quantitative comparison behind the paper's
`B_n log B_n = exp(o(n))` versus `log W_n ≥ c 2^(n-1) - O(1)`. -/
theorem envelope_threshold (A N₁ : ℕ) :
    ∃ N₃, ∀ n, N₃ ≤ n →
      (4 * ((O.Hmax (n + 1) + 2) ^ A) ^ 2 + 3) * 2 ^ N₁ ≤ 2 ^ n := by
  obtain ⟨K, hK, hKle⟩ := O.Hmax_pow_two_le A
  have hlim : Tendsto
      (fun n : ℕ ↦ (4 * K * (3 / 2) * 2 ^ N₁) * (3 / 4 : ℝ) ^ n
        + (3 * 2 ^ N₁ : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ (3 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using (h1.const_mul (4 * K * (3 / 2) * 2 ^ N₁)).add
      (h2.const_mul ((3 : ℝ) * 2 ^ N₁))
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp hlim 1 (by norm_num)
  refine ⟨N₃, fun n hn ↦ ?_⟩
  have hf := hN₃ n hn
  rw [Real.dist_eq, sub_zero] at hf
  have hflt : (4 * K * (3 / 2) * 2 ^ N₁) * (3 / 4 : ℝ) ^ n
      + (3 * 2 ^ N₁ : ℝ) * (1 / 2 : ℝ) ^ n ≤ 1 := (abs_lt.mp hf).2.le
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hmul := mul_le_mul_of_nonneg_right hflt h2n.le
  have hid : ((4 * K * (3 / 2) * 2 ^ N₁) * (3 / 4 : ℝ) ^ n
      + (3 * 2 ^ N₁ : ℝ) * (1 / 2 : ℝ) ^ n) * (2 : ℝ) ^ n
      = (4 * K * (3 / 2) * 2 ^ N₁) * (3 / 2 : ℝ) ^ n + (3 * 2 ^ N₁ : ℝ) := by
    rw [add_mul]
    congr 1
    · rw [mul_assoc, ← mul_pow]; norm_num
    · rw [mul_assoc, ← mul_pow]; norm_num
  rw [hid, one_mul] at hmul
  have hB := hKle (n + 1)
  have hKpow : (0 : ℝ) ≤ (2 : ℝ) ^ N₁ := by positivity
  have hreal : (((4 * ((O.Hmax (n + 1) + 2) ^ A) ^ 2 + 3) * 2 ^ N₁ : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ n := by
    have hexp : (K * (3 / 2 : ℝ) ^ (n + 1)) = (K * (3 / 2)) * (3 / 2 : ℝ) ^ n := by
      rw [pow_succ]; ring
    have hstep : ((((O.Hmax (n + 1) + 2) ^ A : ℕ) : ℝ)) ^ 2
        ≤ (K * (3 / 2)) * (3 / 2 : ℝ) ^ n := by
      rw [← hexp]; exact hB
    have hmono := mul_le_mul_of_nonneg_left hstep
      (by positivity : (0 : ℝ) ≤ 4 * 2 ^ N₁)
    calc (((4 * ((O.Hmax (n + 1) + 2) ^ A) ^ 2 + 3) * 2 ^ N₁ : ℕ) : ℝ)
        = (4 * 2 ^ N₁) * ((((O.Hmax (n + 1) + 2) ^ A : ℕ) : ℝ)) ^ 2
          + (3 * 2 ^ N₁ : ℝ) := by push_cast; ring
    _ ≤ (4 * 2 ^ N₁) * ((K * (3 / 2)) * (3 / 2 : ℝ) ^ n) + (3 * 2 ^ N₁ : ℝ) := by
        linarith [hmono]
    _ = (4 * K * (3 / 2) * 2 ^ N₁) * (3 / 2 : ℝ) ^ n + (3 * 2 ^ N₁ : ℝ) := by ring
    _ ≤ (2 : ℝ) ^ n := hmul
  have hcast : (((2 : ℕ) ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  rw [← hcast] at hreal
  exact_mod_cast hreal

/-! ### `long243:res:oddpowersupply` -/

/-- **Large odd prime powers in the reduced denominator, natural exponent.**

For every natural `A` and every sufficiently large `n`, the reduced
denominator `v n` has an odd prime-power divisor `p ^ k > (Hmax n + 2) ^ A`.
The prime `p` may depend on `n`; no stable-gcd or prime-arrival assumption
is imposed. -/
theorem oddPrimePower_supply_nat (A : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧
      p ^ k ∣ O.v n ∧ (O.Hmax n + 2) ^ A < p ^ k := by
  obtain ⟨N₁, Aq, hAq4, hAqdef, hdbl⟩ :=
    quadratic_double_exponential_bounds O.a O.a_strictMono O.a_pos O.growth
  obtain ⟨N₂, hN₂⟩ := O.oddPart_lower
  obtain ⟨N₃, hN₃⟩ := O.envelope_threshold A N₁
  refine ⟨max (max N₁ N₂) N₃ + 1, fun n hn ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hj1 : N₁ ≤ j := by omega
  have hj2 : N₂ ≤ j := by omega
  have hj3 : N₃ ≤ j := by omega
  by_contra hcon
  push_neg at hcon
  have hW0 : O.oddPart (j + 1) ≠ 0 := (O.oddPart_pos (j + 1)).ne'
  have hB1 : 1 ≤ (O.Hmax (j + 1) + 2) ^ A := Nat.one_le_pow _ _ (by omega)
  have hWle : O.oddPart (j + 1) ≤ ((O.Hmax (j + 1) + 2) ^ A) ^ ((O.Hmax (j + 1) + 2) ^ A + 1) := by
    refine le_pow_of_primePow_le hW0 hB1 (fun p hp ↦ ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvdW : p ∣ O.oddPart (j + 1) := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro h
      subst h
      exact O.two_not_dvd_oddPart (j + 1) hpdvdW
    have hk1 : 1 ≤ (O.oddPart (j + 1)).factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp hW0, pow_one]
      exact hpdvdW
    have hpk : p ^ ((O.oddPart (j + 1)).factorization p) ∣ O.v (j + 1) :=
      dvd_trans ((hpp.pow_dvd_iff_le_factorization hW0).mpr le_rfl) (O.oddPart_dvd (j + 1))
    exact hcon p _ hpp hp2 hk1 hpk
  have hBB : ((O.Hmax (j + 1) + 2) ^ A) ^ ((O.Hmax (j + 1) + 2) ^ A + 1)
      ≤ 2 ^ (4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2) := by
    have h1 : (O.Hmax (j + 1) + 2) ^ A ≤ 2 ^ ((O.Hmax (j + 1) + 2) ^ A) :=
      Nat.le_of_lt Nat.lt_two_pow_self
    calc ((O.Hmax (j + 1) + 2) ^ A) ^ ((O.Hmax (j + 1) + 2) ^ A + 1)
        ≤ (2 ^ ((O.Hmax (j + 1) + 2) ^ A)) ^ ((O.Hmax (j + 1) + 2) ^ A + 1) :=
          Nat.pow_le_pow_left h1 _
    _ = 2 ^ ((O.Hmax (j + 1) + 2) ^ A * ((O.Hmax (j + 1) + 2) ^ A + 1)) := by
        rw [← pow_mul]
    _ ≤ 2 ^ (4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hA1 : O.a j ≤ 4 * O.oddPart (j + 1) := hN₂ j hj2
  have hupper : O.a j ≤ 4 * 2 ^ (4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2) := by omega
  have hthr : 4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2 + 3 ≤ 2 ^ (j - N₁) := by
    have h := hN₃ j hj3
    have hsplit : (2 : ℕ) ^ j = 2 ^ N₁ * 2 ^ (j - N₁) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit] at h
    have h2 : (0 : ℕ) < 2 ^ N₁ := pow_pos (by norm_num) _
    have h3 : 2 ^ N₁ * (4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2 + 3)
        ≤ 2 ^ N₁ * 2 ^ (j - N₁) := by rw [Nat.mul_comm]; exact h
    exact Nat.le_of_mul_le_mul_left h3 h2
  have hlower : 2 * 2 ^ (2 ^ (j - N₁)) ≤ O.a j := by
    have h := (hdbl (j - N₁)).1
    rwa [show N₁ + (j - N₁) = j by omega] at h
  have hmono : (2 : ℕ) ^ (4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2 + 3) ≤ 2 ^ (2 ^ (j - N₁)) :=
    Nat.pow_le_pow_right (by norm_num) hthr
  have he : (2 : ℕ) ^ (4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2 + 3)
      = 2 ^ (4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2) * 8 := by
    rw [pow_add]; norm_num
  rw [he] at hmono
  have hx : (0 : ℕ) < 2 ^ (4 * ((O.Hmax (j + 1) + 2) ^ A) ^ 2) := pow_pos (by norm_num) _
  omega

/-- **`long243:res:oddpowersupply`: large odd prime powers in the reduced
denominator.**

Under the standing hypotheses, for every fixed real `A > 0` and every
sufficiently large `n`, the reduced denominator `v n` has an odd prime-power
divisor `Q = p ^ k` with `Q > (H n + 2) ^ A`, where `H n = max_{j ≤ n} C j`.
The prime `p` may depend on `n`; no stable-gcd or prime-arrival assumption is
imposed. -/
theorem oddPrimePower_supply (A : ℝ) (hA : 0 < A) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧ Odd (p ^ k) ∧
      p ^ k ∣ O.v n ∧ ((O.Hmax n : ℝ) + 2) ^ A < ((p ^ k : ℕ) : ℝ) := by
  obtain ⟨N, hN⟩ := O.oddPrimePower_supply_nat ⌈A⌉₊
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨p, k, hp, hp2, hk, hdvd, hlt⟩ := hN n hn
  refine ⟨p, k, hp, hp2, hk, (hp.odd_of_ne_two hp2).pow, hdvd, ?_⟩
  have hbase : (1 : ℝ) ≤ (O.Hmax n : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (O.Hmax n : ℝ) := Nat.cast_nonneg _
    linarith
  calc ((O.Hmax n : ℝ) + 2) ^ A
      ≤ ((O.Hmax n : ℝ) + 2) ^ ((⌈A⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil A)
  _ = ((O.Hmax n : ℝ) + 2) ^ (⌈A⌉₊ : ℕ) := Real.rpow_natCast _ _
  _ = (((O.Hmax n + 2) ^ ⌈A⌉₊ : ℕ) : ℝ) := by push_cast; ring
  _ < ((p ^ k : ℕ) : ℝ) := by exact_mod_cast hlt

end StandingOrbit

/-! ## 6. `long243:res:unitrecord`: unit record increments -/

theorem runningMax_le_runningMax {U V : ℕ → ℕ} (h : ∀ k, U k ≤ V k) :
    ∀ n, runningMax U n ≤ runningMax V n := by
  intro n
  induction n with
  | zero => exact h 0
  | succ n ih => exact max_le_max ih (h (n + 1))

namespace StandingOrbit

variable (O : StandingOrbit)

theorem R_le_Hmax (n : ℕ) : O.R n ≤ O.Hmax n :=
  runningMax_le_runningMax (fun k ↦ O.u_le_C k) n

/-- The fresh prime-power supply required by
`recordIncrementOne_sylvesterNext_eventually`, discharged from
`long243:res:oddpowersupply` with `A = 1`. -/
theorem primePower_supply :
    ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ O.v s ∧ runningMax O.u s + 3 ≤ p ^ l := by
  obtain ⟨Ns, hNs⟩ := O.oddPrimePower_supply_nat 1
  intro M
  refine ⟨max M Ns, le_max_left _ _, ?_⟩
  obtain ⟨p, k, hp, _, hk, hdvd, hlt⟩ := hNs (max M Ns) (le_max_right _ _)
  refine ⟨p, k, hp, hk, hdvd, ?_⟩
  have hR : runningMax O.u (max M Ns) ≤ O.Hmax (max M Ns) := O.R_le_Hmax _
  rw [pow_one] at hlt
  omega

/-- **`long243:res:unitrecord` (i): unit record increments force the Sylvester
recurrence.**

Under the standing hypotheses, if `R (n+1) - R n ≤ 1` for all large `n`, then
`a (n+1) = a n ^ 2 - a n + 1` for all large `n`.  No hypothesis is placed on
drawdowns, on record-setting jumps, or on the cancellation factors `h n`. -/
theorem unitRecordIncrement_sylvesterNext
    (hinc : ∃ N, ∀ n, N ≤ n → O.R (n + 1) - O.R n ≤ 1) :
    ∃ M, ∀ n, M ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  obtain ⟨Ni, hNi⟩ := hinc
  obtain ⟨Nc, hNc⟩ := O.redErr_vanishing 2
  obtain ⟨M, hM⟩ :=
    recordIncrementOne_sylvesterNext_eventually O.a O.u O.v O.w O.canc O.redErr
      (max Ni Nc)
      (fun n _ ↦ O.v_pos n) (fun n _ ↦ O.coprime_u_v n) (fun n _ ↦ O.w_add_v n)
      (fun n _ ↦ O.w_pos n) (fun n _ ↦ O.num_step n) (fun n _ ↦ O.den_step n)
      (fun n _ ↦ O.redErr_eq n)
      (fun n hn ↦ hNc n (le_trans (le_max_right Ni Nc) hn))
      (fun K ↦ O.redErr_vanishing K)
      (fun n hn ↦ by
        have h : runningMax O.u (n + 1) - runningMax O.u n ≤ 1 :=
          hNi n (le_trans (le_max_left Ni Nc) hn)
        have hmono : runningMax O.u n ≤ runningMax O.u (n + 1) := le_max_left _ _
        show runningMax O.u (n + 1) ≤ runningMax O.u n + 1
        omega)
      O.primePower_supply
  exact ⟨M, fun n hn ↦ by simpa [sylvesterNext] using hM n hn⟩

/-- A Sylvester tail satisfies `D n = (a n - 1) C n` exactly, because its real
tail is `1 / (a n - 1)`. -/
theorem sylvester_tail_identity
    (hrec : ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) :
    ∃ N, ∀ n, N ≤ n → 2 ≤ O.a n ∧ (O.a n - 1) * O.C n = O.D n := by
  obtain ⟨Nr, hNr⟩ := hrec
  obtain ⟨Na, hNa⟩ := strictMono_eventually_ge_two O.a O.a_strictMono O.a_pos
  refine ⟨max Nr Na, fun n hn ↦ ?_⟩
  have hna : 2 ≤ O.a n := hNa n (le_trans (le_max_right Nr Na) hn)
  have htail := realTail_eq_of_eventual_sylvester O.a O.a_strictMono O.a_pos
    O.hasSum.summable (max Nr Na)
    (fun m hm ↦ hNa m (le_trans (le_max_right Nr Na) hm))
    (fun m hm ↦ hNr m (le_trans (le_max_left Nr Na) hm))
  have hr := O.C_repr n
  rw [htail n hn] at hr
  have haR : (1 : ℝ) < (O.a n : ℝ) := by exact_mod_cast (show 1 < O.a n by omega)
  have hane : (O.a n : ℝ) - 1 ≠ 0 := by linarith
  have hDC : ((O.a n : ℝ) - 1) * (O.C n : ℝ) = (O.D n : ℝ) := by
    rw [hr]
    field_simp
  have hcastsub : ((O.a n - 1 : ℕ) : ℝ) = (O.a n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ O.a n := by omega
    push_cast [Nat.cast_sub this]
    ring
  refine ⟨hna, ?_⟩
  have : (((O.a n - 1) * O.C n : ℕ) : ℝ) = ((O.D n : ℕ) : ℝ) := by
    push_cast [hcastsub]
    exact hDC
  exact_mod_cast this

/-- A Sylvester tail has reduced numerator `1`. -/
theorem u_eq_one_of_eventual_sylvester
    (hrec : ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) :
    ∃ N, ∀ n, N ≤ n → O.u n = 1 := by
  obtain ⟨N, hN⟩ := O.sylvester_tail_identity hrec
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨_, hnat⟩ := hN n hn
  have hdvd : O.C n ∣ O.D n := ⟨O.a n - 1, by rw [← hnat]; ring⟩
  have hG : O.G n = O.C n := Nat.gcd_eq_left hdvd
  show O.C n / O.G n = 1
  rw [hG]
  exact Nat.div_self (O.C_pos n)

/-- A Sylvester tail has reduced numerator `1`, reduced denominator `a n - 1`,
zero reduced error and hence `𝒜 n = 0`.

This is the "`u n = 1` and `m n = 0` eventually, so `𝒜 n → 0`" half of
`long243:res:recordamplified`. -/
theorem reduced_trivial_of_eventual_sylvester
    (hrec : ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) :
    ∃ N, ∀ n, N ≤ n →
      O.u n = 1 ∧ O.v n = O.a n - 1 ∧ O.redErr n = 0 ∧ O.negPart n = 0 ∧ O.amp n = 0 := by
  obtain ⟨N, hN⟩ := O.sylvester_tail_identity hrec
  obtain ⟨N', hN'⟩ := O.u_eq_one_of_eventual_sylvester hrec
  refine ⟨max N N', fun n hn ↦ ?_⟩
  obtain ⟨hna, hnat⟩ := hN n (le_trans (le_max_left N N') hn)
  have hu : O.u n = 1 := hN' n (le_trans (le_max_right N N') hn)
  have hGC : O.G n = O.C n := by
    have h := O.u_mul n
    rw [hu, Nat.one_mul] at h
    exact h
  have hvC : O.v n * O.C n = O.D n := by
    have h := O.v_mul n
    rwa [hGC] at h
  have hv : O.v n = O.a n - 1 :=
    Nat.eq_of_mul_eq_mul_right (O.C_pos n) (by rw [hvC, hnat])
  have hev : O.redErr n = 0 := by
    have h1 : (1 : ℕ) ≤ O.a n := by omega
    rw [redErr, hu, hv]
    push_cast [Nat.cast_sub h1]
    ring
  have hm : O.negPart n = 0 := by
    rw [negPart, hev]
    rfl
  refine ⟨hu, hv, hev, hm, ?_⟩
  rw [amp, hm]
  simp

/-- **`long243:res:unitrecord` (ii): the finiteness criterion.**

The sequence is eventually Sylvester if and only if
`#{n : R (n+1) - R n ≥ 2}` is finite. -/
theorem unitRecordIncrement_criterion :
    (∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ↔
      {n : ℕ | 2 ≤ O.R (n + 1) - O.R n}.Finite := by
  constructor
  · intro hrec
    obtain ⟨N, hN⟩ := O.u_eq_one_of_eventual_sylvester hrec
    have hconst : ∀ n, N ≤ n → O.R (n + 1) = O.R n := by
      intro n hn
      have h1 : O.u (n + 1) = 1 := hN (n + 1) (by omega)
      have h2 : 1 ≤ runningMax O.u n :=
        le_trans (O.u_pos 0) (le_runningMax O.u (Nat.zero_le n))
      show max (runningMax O.u n) (O.u (n + 1)) = runningMax O.u n
      rw [h1]
      omega
    refine Set.Finite.subset (Set.finite_Iio N) (fun n hn ↦ ?_)
    simp only [Set.mem_setOf_eq] at hn
    by_contra hcon
    have hge : N ≤ n := by
      simp only [Set.mem_Iio] at hcon
      omega
    have := hconst n hge
    omega
  · intro hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    refine O.unitRecordIncrement_sylvesterNext ⟨N + 1, fun n hn ↦ ?_⟩
    by_contra hcon
    have hmem : n ∈ {n : ℕ | 2 ≤ O.R (n + 1) - O.R n} := by
      simp only [Set.mem_setOf_eq]
      omega
    have := hN hmem
    omega

end StandingOrbit

end ErdosProblems.Erdos243.PaperCompleteR21

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply_nat
#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.unitRecordIncrement_sylvesterNext
#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.unitRecordIncrement_criterion

