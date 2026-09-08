import ErdosProblems.Erdos68.PaperCompleteDyadicEnclosure
import Mathlib.Tactic.FieldSimp

/-!
# Round 8: sound finite arithmetic consumers

The Farey certificate replaces a long continued-fraction proof trace by two
bounding fractions with determinant one. Continued fractions are used only
by the producer to find these fractions; soundness does not depend on that
algorithm, on a quotient count, or on reducedness of the input `a/q`.
The factorial-grid certificate excludes one integer grid directly, without
requiring the historical full carry census.

All validity predicates are decidable finite integer arithmetic. This file
proves their consequences, but does not assert validity of the large data.
Status: proof text, not elaborated in the return environment.
-/

namespace ErdosProblems.Erdos68.PaperComplete.FiniteLead


/-- Algebra behind the GMP producer's quotient update. The correction may be
negative; the producer then uses floor division, not truncation toward zero. -/
theorem quotient_remainder_transport
    (scale d q r b t n : ℤ)
    (hdiv : scale = q * d + r) (hsplit : q = n * b + t) :
    scale = b * (n * d + (n - 1)) + (r + t * d - b * (n - 1)) := by
  calc
    scale = q * d + r := hdiv
    _ = b * (n * d + (n - 1)) + (r + t * d - b * (n - 1)) := by
      rw [hsplit]
      ring

/-- Exact quotient/remainder data determine the Nat division in floorPrefix.
Lean v4.29.1: Init/Data/Nat/Div/Basic.lean, Nat.div_eq_of_lt_le. -/
theorem quotient_of_remainder
    (scale d q r : ℕ) (heq : scale = q * d + r) (hr : r < d) :
    scale / d = q := by
  apply Nat.div_eq_of_lt_le
  · nlinarith only [heq]
  · nlinarith only [heq, hr]

structure FareyData where
  leftNum : ℕ
  leftDen : ℕ
  rightNum : ℕ
  rightDen : ℕ
  deriving Repr

/-- The exact finite Farey predicate; the interval contains no hypotheses
about a hypothetical rational denominator. -/
def FareyData.Valid (f : FareyData) (c : DyadicData) (bound : ℕ) : Prop :=
  0 < f.leftDen ∧ 0 < f.rightDen ∧
  f.leftDen * f.rightNum = f.leftNum * f.rightDen + 1 ∧
  f.leftNum * (2 ^ c.bits) ≤ c.lower * f.leftDen ∧
  c.upper * f.rightDen ≤ f.rightNum * (2 ^ c.bits) ∧
  bound ≤ f.leftDen + f.rightDen

instance (f : FareyData) (c : DyadicData) (bound : ℕ) :
    Decidable (f.Valid c bound) := inferInstanceAs
  (Decidable (0 < f.leftDen ∧ 0 < f.rightDen ∧
    f.leftDen * f.rightNum = f.leftNum * f.rightDen + 1 ∧
    f.leftNum * (2 ^ c.bits) ≤ c.lower * f.leftDen ∧
    c.upper * f.rightDen ≤ f.rightNum * (2 ^ c.bits) ∧
    bound ≤ f.leftDen + f.rightDen))

/-- An interior rational of a determinant-one interval has denominator at
least the sum of the two endpoint denominators. No coprimality premise. -/
theorem farey_denominator_lower_bound
    (A B C E : ℕ) (hB : 0 < B) (hE : 0 < E)
    (hdet : B * C = A * E + 1)
    (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hleft : (A : ℝ) / B < (a : ℝ) / q)
    (hright : (a : ℝ) / q < (C : ℝ) / E) : B + E ≤ q := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean,
  -- exposed by Mathlib/Algebra/Order/Field/Basic.lean.
  have hcrossL : (A : ℝ) * q < (a : ℝ) * B :=
    (div_lt_div_iff₀ hBR hqR).mp hleft
  have hcrossR : (a : ℝ) * E < (C : ℝ) * q :=
    (div_lt_div_iff₀ hqR hER).mp hright
  let u : ℤ := a * (B : ℤ) - (A : ℤ) * q
  let v : ℤ := (C : ℤ) * q - a * E
  have huR : (0 : ℝ) < (u : ℝ) := by
    dsimp [u]
    push_cast
    linarith only [hcrossL]
  have hvR : (0 : ℝ) < (v : ℝ) := by
    dsimp [v]
    push_cast
    linarith only [hcrossR]
  have huZ : (0 : ℤ) < u := by exact_mod_cast huR
  have hvZ : (0 : ℤ) < v := by exact_mod_cast hvR
  have hu : (1 : ℤ) ≤ u := by omega
  have hv : (1 : ℤ) ≤ v := by omega
  have hdetZ : (B : ℤ) * C = (A : ℤ) * E + 1 := by
    exact_mod_cast hdet
  have hdetq : ((B : ℤ) * C) * (q : ℤ) =
      ((A : ℤ) * E + 1) * (q : ℤ) :=
    congrArg (fun z : ℤ => z * (q : ℤ)) hdetZ
  have hid : (q : ℤ) = (E : ℤ) * u + (B : ℤ) * v := by
    dsimp [u, v]
    nlinarith only [hdetq]
  have hB0 : (0 : ℤ) ≤ B := by positivity
  have hE0 : (0 : ℤ) ≤ E := by positivity
  have hEu : (E : ℤ) * 1 ≤ (E : ℤ) * u :=
    mul_le_mul_of_nonneg_left hu hE0
  have hBv : (B : ℤ) * 1 ≤ (B : ℤ) * v :=
    mul_le_mul_of_nonneg_left hv hB0
  have hboundZ : (B : ℤ) + (E : ℤ) ≤ (q : ℤ) := by
    linarith only [hid, hEu, hBv]
  exact_mod_cast hboundZ

/-- The dyadic and Farey finite predicates imply the size exclusion. -/
theorem denominator_bound_of_farey
    {c : DyadicData} {f : FareyData} {bound : ℕ}
    (hc : c.Valid) (hf : f.Valid c bound)
    (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : _root_.Erdos68.factorialGapSeries = (a : ℝ) / q) : bound ≤ q := by
  obtain ⟨hB, hE, hdet, hleft, hright, hbound⟩ := hf
  obtain ⟨hlo, hhi⟩ := DyadicData.sound hc
  have hBR : (0 : ℝ) < f.leftDen := by exact_mod_cast hB
  have hER : (0 : ℝ) < f.rightDen := by exact_mod_cast hE
  have hscale : (0 : ℝ) < (2 ^ c.bits : ℕ) := by positivity
  have hleftR : (f.leftNum : ℝ) * (2 ^ c.bits : ℕ) ≤
      (c.lower : ℝ) * f.leftDen := by exact_mod_cast hleft
  have hrightR : (c.upper : ℝ) * f.rightDen ≤
      (f.rightNum : ℝ) * (2 ^ c.bits : ℕ) := by exact_mod_cast hright
  have hleftEnd : (f.leftNum : ℝ) / f.leftDen ≤
      (c.lower : ℝ) / (2 ^ c.bits : ℕ) :=
    (div_le_div_iff₀ hBR hscale).mpr hleftR
  have hrightEnd : (c.upper : ℝ) / (2 ^ c.bits : ℕ) ≤
      (f.rightNum : ℝ) / f.rightDen :=
    (div_le_div_iff₀ hscale hER).mpr hrightR
  have hleftInside : (f.leftNum : ℝ) / f.leftDen < (a : ℝ) / q := by
    rw [← hS]
    exact hleftEnd.trans_lt hlo
  have hrightInside : (a : ℝ) / q < (f.rightNum : ℝ) / f.rightDen := by
    rw [← hS]
    exact hhi.trans_le hrightEnd
  exact hbound.trans (farey_denominator_lower_bound
    f.leftNum f.leftDen f.rightNum f.rightDen hB hE hdet a q hq
    hleftInside hrightInside)

/-- `n!` times the entire dyadic interval is strictly inside one open unit cell.
The cell is computed from the lower endpoint, not supplied as a real premise. -/
def GridCellTarget (c : DyadicData) (n : ℕ) : Prop :=
  let k := n.factorial * c.lower / (2 ^ c.bits)
  k * (2 ^ c.bits) < n.factorial * c.lower ∧
  n.factorial * c.upper < (k + 1) * (2 ^ c.bits)

instance (c : DyadicData) (n : ℕ) : Decidable (GridCellTarget c n) :=
  inferInstanceAs (Decidable
    ((n.factorial * c.lower / (2 ^ c.bits)) * (2 ^ c.bits) < n.factorial * c.lower ∧
      n.factorial * c.upper <
        (n.factorial * c.lower / (2 ^ c.bits) + 1) * (2 ^ c.bits)))

/-- Exact finite grid exclusion. It does not assert the grid predicate. -/
theorem not_dvd_factorial_of_grid
    {c : DyadicData} {n : ℕ} (hc : c.Valid) (hg : GridCellTarget c n)
    (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : _root_.Erdos68.factorialGapSeries = (a : ℝ) / q) :
    ¬ q ∣ n.factorial := by
  obtain ⟨hlo, hhi⟩ := DyadicData.sound hc
  let k : ℕ := n.factorial * c.lower / (2 ^ c.bits)
  change k * (2 ^ c.bits) < n.factorial * c.lower ∧
    n.factorial * c.upper < (k + 1) * (2 ^ c.bits) at hg
  have hscale : (0 : ℝ) < (2 ^ c.bits : ℕ) := by positivity
  have hF : (0 : ℝ) < n.factorial := by positivity
  have hglo : (k : ℝ) * (2 ^ c.bits : ℕ) <
      (n.factorial : ℝ) * c.lower := by exact_mod_cast hg.1
  have hghi : (n.factorial : ℝ) * c.upper <
      ((k : ℝ) + 1) * (2 ^ c.bits : ℕ) := by exact_mod_cast hg.2
  have hklo : (k : ℝ) < (n.factorial : ℝ) * _root_.Erdos68.factorialGapSeries := by
    calc
      (k : ℝ) < (n.factorial : ℝ) * c.lower / (2 ^ c.bits : ℕ) :=
        (lt_div_iff₀ hscale).mpr hglo
      _ = (n.factorial : ℝ) * ((c.lower : ℝ) / (2 ^ c.bits : ℕ)) := by ring
      _ < (n.factorial : ℝ) * _root_.Erdos68.factorialGapSeries :=
        mul_lt_mul_of_pos_left hlo hF
  have hkhi : (n.factorial : ℝ) * _root_.Erdos68.factorialGapSeries < (k : ℝ) + 1 := by
    calc
      (n.factorial : ℝ) * _root_.Erdos68.factorialGapSeries <
          (n.factorial : ℝ) * ((c.upper : ℝ) / (2 ^ c.bits : ℕ)) :=
        mul_lt_mul_of_pos_left hhi hF
      _ = (n.factorial : ℝ) * c.upper / (2 ^ c.bits : ℕ) := by ring
      _ < (k : ℝ) + 1 := (div_lt_iff₀ hscale).mpr hghi
  intro hdiv
  obtain ⟨b, hb⟩ := hdiv
  have hbR : (n.factorial : ℝ) = (q : ℝ) * b := by exact_mod_cast hb
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hFx : (n.factorial : ℝ) * _root_.Erdos68.factorialGapSeries =
      ((a * (b : ℤ) : ℤ) : ℝ) := by
    rw [hS, hbR]
    push_cast
    field_simp [ne_of_gt hqR]
    all_goals ring
  rw [hFx] at hklo hkhi
  have hzlo : (k : ℤ) < a * (b : ℤ) := by exact_mod_cast hklo
  have hzhi : a * (b : ℤ) < (k : ℤ) + 1 := by exact_mod_cast hkhi
  omega


/-- Natural-number version of the independent descending producer step.
Unlike the forward correction, its temporary remainder is never negative.
Lean v4.29.1: Init/Data/Nat/Div/Basic.lean supplies `Nat.div_add_mod` and
`Nat.mod_lt`; `quotient_of_remainder` above supplies quotient uniqueness. -/
theorem reverse_quotient_remainder_transport
    (scale n d q r : ℕ) (hd : 0 < d)
    (hrep : scale = q * (n * d + (n - 1)) + r) :
    scale / d = n * q + (r + (n - 1) * q) / d ∧
      scale % d = (r + (n - 1) * q) % d := by
  have hround :
      d * ((r + (n - 1) * q) / d) + (r + (n - 1) * q) % d =
        r + (n - 1) * q := Nat.div_add_mod (r + (n - 1) * q) d
  have hsplit : scale =
      (n * q + (r + (n - 1) * q) / d) * d +
        (r + (n - 1) * q) % d := by
    calc
      scale = (n * q) * d + (r + (n - 1) * q) := by
        rw [hrep]
        ring
      _ = (n * q) * d +
          (d * ((r + (n - 1) * q) / d) + (r + (n - 1) * q) % d) := by
        rw [hround]
      _ = _ := by ring
  have hquot : scale / d = n * q + (r + (n - 1) * q) / d :=
    quotient_of_remainder scale d
      (n * q + (r + (n - 1) * q) / d)
      ((r + (n - 1) * q) % d) hsplit (Nat.mod_lt _ hd)
  have hscale : d * (scale / d) + scale % d = scale :=
    Nat.div_add_mod scale d
  have hrem : scale % d = (r + (n - 1) * q) % d := by
    rw [hquot] at hscale
    nlinarith only [hscale, hsplit]
  exact ⟨hquot, hrem⟩

/-- Two additional integer comparisons exhibit the mediant strictly inside
an open dyadic interval. Together with `Valid`, they certify that the sum of
the Farey denominators is the EXACT minimum, not just a lower bound. -/
def FareyData.Sharp (f : FareyData) (c : DyadicData) : Prop :=
  c.lower * (f.leftDen + f.rightDen) <
      (f.leftNum + f.rightNum) * (2 ^ c.bits) ∧
    (f.leftNum + f.rightNum) * (2 ^ c.bits) <
      c.upper * (f.leftDen + f.rightDen)

instance (f : FareyData) (c : DyadicData) : Decidable (f.Sharp c) :=
  inferInstanceAs (Decidable
    (c.lower * (f.leftDen + f.rightDen) <
        (f.leftNum + f.rightNum) * (2 ^ c.bits) ∧
      (f.leftNum + f.rightNum) * (2 ^ c.bits) <
        c.upper * (f.leftDen + f.rightDen)))

/-- Sharp minimum-denominator certificate for the OPEN dyadic interval.
The first conclusion bounds every representation, not just reduced ones.
The second and third conclusions give the attaining representation.
No claim that the attaining rational equals the factorial-gap series is made.
The ordered-field comparison lemmas are in the pinned
Mathlib/Algebra/Order/Field/Basic.lean import chain. -/
theorem exact_interval_denominator_of_sharp
    {c : DyadicData} {f : FareyData} {bound : ℕ}
    (hf : f.Valid c bound) (hs : f.Sharp c) :
    (∀ (a : ℤ) (q : ℕ), 0 < q →
      (c.lower : ℝ) / (2 ^ c.bits : ℕ) < (a : ℝ) / q →
      (a : ℝ) / q < (c.upper : ℝ) / (2 ^ c.bits : ℕ) →
      f.leftDen + f.rightDen ≤ q) ∧
    (c.lower : ℝ) / (2 ^ c.bits : ℕ) <
      ((f.leftNum + f.rightNum : ℕ) : ℝ) /
        ((f.leftDen + f.rightDen : ℕ) : ℝ) ∧
    ((f.leftNum + f.rightNum : ℕ) : ℝ) /
        ((f.leftDen + f.rightDen : ℕ) : ℝ) <
      (c.upper : ℝ) / (2 ^ c.bits : ℕ) := by
  obtain ⟨hB, hE, hdet, hleft, hright, _hbound⟩ := hf
  have hBR : (0 : ℝ) < f.leftDen := by exact_mod_cast hB
  have hER : (0 : ℝ) < f.rightDen := by exact_mod_cast hE
  have hscale : (0 : ℝ) < (2 ^ c.bits : ℕ) := by positivity
  have hsumN : 0 < f.leftDen + f.rightDen := by omega
  have hsum : (0 : ℝ) < (f.leftDen + f.rightDen : ℕ) := by
    exact_mod_cast hsumN
  have hleftR : (f.leftNum : ℝ) * (2 ^ c.bits : ℕ) ≤
      (c.lower : ℝ) * f.leftDen := by exact_mod_cast hleft
  have hrightR : (c.upper : ℝ) * f.rightDen ≤
      (f.rightNum : ℝ) * (2 ^ c.bits : ℕ) := by exact_mod_cast hright
  have hleftEnd : (f.leftNum : ℝ) / f.leftDen ≤
      (c.lower : ℝ) / (2 ^ c.bits : ℕ) :=
    (div_le_div_iff₀ hBR hscale).mpr hleftR
  have hrightEnd : (c.upper : ℝ) / (2 ^ c.bits : ℕ) ≤
      (f.rightNum : ℝ) / f.rightDen :=
    (div_le_div_iff₀ hscale hER).mpr hrightR
  have hmin : ∀ (a : ℤ) (q : ℕ), 0 < q →
      (c.lower : ℝ) / (2 ^ c.bits : ℕ) < (a : ℝ) / q →
      (a : ℝ) / q < (c.upper : ℝ) / (2 ^ c.bits : ℕ) →
      f.leftDen + f.rightDen ≤ q := by
    intro a q hq hlo hhi
    exact farey_denominator_lower_bound f.leftNum f.leftDen
      f.rightNum f.rightDen hB hE hdet a q hq
      (hleftEnd.trans_lt hlo) (hhi.trans_le hrightEnd)
  have hmedL : (c.lower : ℝ) * ((f.leftDen + f.rightDen : ℕ) : ℝ) <
      ((f.leftNum + f.rightNum : ℕ) : ℝ) * (2 ^ c.bits : ℕ) := by
    exact_mod_cast hs.1
  have hmedR : ((f.leftNum + f.rightNum : ℕ) : ℝ) * (2 ^ c.bits : ℕ) <
      (c.upper : ℝ) * ((f.leftDen + f.rightDen : ℕ) : ℝ) := by
    exact_mod_cast hs.2
  exact ⟨hmin, (div_lt_div_iff₀ hscale hsum).mpr hmedL,
    (div_lt_div_iff₀ hsum hscale).mpr hmedR⟩

/-- The same finite predicates give their full denominator sum as a bound;
there is no need to discard it in favour of the paper's smaller power of two. -/
theorem denominator_bound_of_farey_sum
    {c : DyadicData} {f : FareyData} {bound : ℕ}
    (hc : c.Valid) (hf : f.Valid c bound)
    (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : _root_.Erdos68.factorialGapSeries = (a : ℝ) / q) :
    f.leftDen + f.rightDen ≤ q := by
  obtain ⟨hB, hE, hdet, hlo, hhi, _hb⟩ := hf
  have hsum : f.Valid c (f.leftDen + f.rightDen) :=
    ⟨hB, hE, hdet, hlo, hhi, le_rfl⟩
  exact denominator_bound_of_farey hc hsum a q hq hS

end ErdosProblems.Erdos68.PaperComplete.FiniteLead
