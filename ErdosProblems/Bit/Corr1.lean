/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.HalfCylinderLargestSkipInduction

/-!
# The late-zone greedy word is a binary expansion

In the late zone `2 * s < 3 * d` the truncated Mersenne weight has exactly two
binary terms,

`truncatedMersenneWeight s d = 2 ^ (2 * s - d) + 4 ^ (s - d)`

(`truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank`).  The leading
terms `2 ^ (2 * s - d)`, for `d` running over the late ranks, are *distinct
powers of two* of exponent at least `s + 1`; the corrections
`4 ^ (s - d) = 2 ^ (2 * (s - d))` all sit strictly below bit `s + 1`, because
`2 * s < 3 * d` forces `2 * (s - d) < s`.

Consequently the descending integer greedy run over the late weights never sees
the corrections when it compares: at each late rank it simply asks whether the
corresponding *bit* of the entering capacity is set.  The only thing that could
spoil this is a borrow out of the low `s + 1` bits, and that is ruled out by the
single side condition

`lateCorrection s d ≤ C % 2 ^ (s + 1)`,

i.e. the low part of the capacity can absorb the whole correction budget
`∑_{k=1}^{s-d} 4 ^ k`.  That side condition is *proved* to propagate through the
recursion, not assumed at every step (`mod_sub_of_le_mod` plus
`testBit_sub_of_le_mod` are the two facts that make the borrow impossible).

## Main results

* `integerGreedyBits_seamWeightsFrom_eq_lateBitWord` — the late-zone greedy word
  is literally `fun d ↦ Nat.testBit C (2 * s - d)`, read off the capacity `C`
  entering the late zone, not off any running remainder.
* `takes_iff_testBit`, `getElem?_eq_testBit` — the pointwise take/skip form.
* `all_true_iff_forall_testBit` — the greedy takes *every* late rank iff every
  bit of `C` in the window `(s, 2 * s - d]` is one; contrapositively a single
  zero bit in that window is a skipped late rank.
* `lateCorrection_lt_two_pow` — the correction budget provably cannot reach the
  compared bits.
* `mem_seamGreedySupport_iff_testBit` — the same statement for the corpus's own
  `seamWordSupport (seamGreedyWord s)`, with `C` the genuine entering remainder
  `lateEntryRemainder s d`.  This is obtained from `integerGreedyBits_append`
  plus `seamWeights_eq_take_append`, which split the actual seam greedy run at
  the first late rank.

All of these statements are conditional on `hlow`.  That side condition is
not universal: `ErdosProblems/Decl/D4.lean` proves
`DeclD4.Seven.not_hlow_seven_five` at `(s,d) = (7,5)`, and
`ErdosProblems/Hlow/H1.lean` proves that `hhigh` still holds there.  Thus the
bit correspondence below is a valid conditional theorem, not a description
available at every late rank.  `ErdosProblems/Hlow/H2.lean` later proves
`seamRemainder_lt_two_pow_of_not_hlow`: failure of `hlow` is itself a
half-point hit certificate, rather than an unresolved obstruction.

## Non-vacuity

Namespace `Concrete` is the anti-vacuity certificate, in two layers.

*Layer 1 (arbitrary capacity).*  `s = 20`, `d = 14` — the first late rank at
`s = 20`, since `2 * 20 < 3 * 14` and `¬ (2 * 20 < 3 * 13)` — and
`C = 87217799`.  All three hypotheses are checked by `decide +kernel`
(`hypotheses_hold`), and both sides of the conclusion are computed
*independently* — the greedy side from the actual `truncatedMersenneWeight`
values, the bit side from the binary expansion of `C` — to the same word
`[true, false, true, false, false, true]`.

*Layer 2 (the real object).*  The genuine remainder produced by the corpus's own
greedy run at `s = 20` is `lateEntryRemainder 20 14 = 67662313`, and it too
satisfies both side conditions (`actual_hypotheses_hold`).  Reading its bits
gives `14 ∈ seamWordSupport (seamGreedyWord 20)` and
`15, 19 ∉ seamWordSupport (seamGreedyWord 20)`, hence `LargestSkipLateAt 20`
(`largestSkipLateAt_twenty`) — the very predicate whose cofinality is
equivalent to `1/2 ∈ mersenneAchievementSet`.  So the theorems below are not
merely satisfiable: they apply to the object of Erdős #257 and produce its
predicate.
-/

namespace Erdos249257

namespace BitCorr

open HalfCylinderIntegerGreedy

/-! ## Bit-level helpers: subtracting inside the low block -/

/-- Subtracting a quantity that already fits inside the low `P` block leaves the
high blocks alone. -/
theorem mod_sub_of_le_mod {A X P : ℕ} (hP : 0 < P) (h : X ≤ A % P) :
    (A - X) % P = A % P - X := by
  have hd := Nat.div_add_mod A P
  have hlt := Nat.mod_lt A hP
  have key : A - X = P * (A / P) + (A % P - X) := by omega
  rw [key, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- Subtracting a quantity that already fits inside the low `p` bits leaves
every bit at index `≥ p` untouched: no borrow escapes the low block. -/
theorem testBit_sub_of_le_mod
    {x a p j : ℕ} (ha : a ≤ x % 2 ^ p) (hj : p ≤ j) :
    Nat.testBit (x - a) j = Nat.testBit x j := by
  have hp : 0 < 2 ^ p := Nat.two_pow_pos p
  have hdm := Nat.div_add_mod x (2 ^ p)
  have hlt : x % 2 ^ p < 2 ^ p := Nat.mod_lt _ hp
  have hsub : x - a = 2 ^ p * (x / 2 ^ p) + (x % 2 ^ p - a) := by omega
  have hzero : (x % 2 ^ p - a) / 2 ^ p = 0 := Nat.div_eq_of_lt (by omega)
  have hdiv : (x - a) / 2 ^ p = x / 2 ^ p := by
    rw [hsub, Nat.mul_add_div hp, hzero, Nat.add_zero]
  have h1 : Nat.testBit ((x - a) / 2 ^ p) (j - p) = Nat.testBit (x - a) j := by
    rw [Nat.testBit_div_two_pow]
    congr 1
    omega
  have h2 : Nat.testBit (x / 2 ^ p) (j - p) = Nat.testBit x j := by
    rw [Nat.testBit_div_two_pow]
    congr 1
    omega
  rw [← h1, ← h2, hdiv]

/-! ## The correction budget -/

/-- Total `4 ^ k` correction carried by the late weights `d, d+1, …, s-1`, i.e.
`∑_{k=1}^{s-d} 4 ^ k`. -/
def lateCorrection (s : ℕ) : ℕ → ℕ
  | d => if h : d < s then 4 ^ (s - d) + lateCorrection s (d + 1) else 0
termination_by d => s - d
decreasing_by omega

theorem lateCorrection_eq_zero {s d : ℕ} (h : s ≤ d) :
    lateCorrection s d = 0 := by
  rw [lateCorrection]
  simp [Nat.not_lt.mpr h]

theorem lateCorrection_eq_cons {s d : ℕ} (h : d < s) :
    lateCorrection s d = 4 ^ (s - d) + lateCorrection s (d + 1) := by
  rw [lateCorrection]
  simp [h]

theorem lateCorrection_succ_le (s d : ℕ) :
    lateCorrection s (d + 1) ≤ lateCorrection s d := by
  by_cases h : d < s
  · rw [lateCorrection_eq_cons h]
    exact Nat.le_add_left _ _
  · rw [lateCorrection_eq_zero (by omega), lateCorrection_eq_zero (by omega)]

/-- Exact closed form `3 * ∑_{k=1}^{s-d} 4 ^ k + 4 = 4 ^ (s-d+1)`. -/
theorem three_mul_lateCorrection_add_four {s d : ℕ} (h : d ≤ s) :
    3 * lateCorrection s d + 4 = 4 * 4 ^ (s - d) := by
  by_cases hlt : d < s
  · have ih := three_mul_lateCorrection_add_four (s := s) (d := d + 1) (by omega)
    have hp : 4 ^ (s - d) = 4 * 4 ^ (s - (d + 1)) := by
      rw [show s - d = (s - (d + 1)) + 1 by omega, pow_succ]
      ring
    rw [lateCorrection_eq_cons hlt]
    omega
  · have hds : d = s := by omega
    subst hds
    rw [lateCorrection_eq_zero (le_refl _), Nat.sub_self, pow_zero]
    norm_num
termination_by s - d
decreasing_by omega

/-- **The corrections cannot reach the compared bits.**  In the late zone the
whole `4 ^ k` budget stays strictly below `2 ^ (s+1)`, while every compared bit
sits at index `≥ s + 1`. -/
theorem lateCorrection_lt_two_pow
    {s d : ℕ} (hds : d ≤ s) (hlate : 2 * s < 3 * d) :
    lateCorrection s d < 2 ^ (s + 1) := by
  have hclosed := three_mul_lateCorrection_add_four (s := s) (d := d) hds
  have hfour : (4 : ℕ) ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  have hexp : 2 * (s - d) + 2 ≤ s + 1 := by omega
  have hmono : (2 : ℕ) ^ (2 * (s - d) + 2) ≤ 2 ^ (s + 1) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hsplit : (2 : ℕ) ^ (2 * (s - d) + 2) = 4 * 2 ^ (2 * (s - d)) := by
    rw [pow_add]
    ring
  omega

/-! ## The bit word -/

/-- The word obtained by reading the bits of `C` at the positions `2 * s - d`,
for `d` running over `d, d+1, …, s-1`. -/
def lateBitWord (s C : ℕ) : ℕ → List Bool
  | d =>
      if h : d < s then
        Nat.testBit C (2 * s - d) :: lateBitWord s C (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

theorem lateBitWord_eq_nil {s C d : ℕ} (h : s ≤ d) :
    lateBitWord s C d = [] := by
  rw [lateBitWord]
  simp [Nat.not_lt.mpr h]

theorem lateBitWord_eq_cons {s C d : ℕ} (h : d < s) :
    lateBitWord s C d =
      Nat.testBit C (2 * s - d) :: lateBitWord s C (d + 1) := by
  rw [lateBitWord]
  simp [h]

theorem lateBitWord_congr {s C C' : ℕ} (d : ℕ)
    (hbits : ∀ e : ℕ, d ≤ e → e < s →
      Nat.testBit C' (2 * s - e) = Nat.testBit C (2 * s - e)) :
    lateBitWord s C' d = lateBitWord s C d := by
  by_cases hds : d < s
  · rw [lateBitWord_eq_cons hds, lateBitWord_eq_cons hds, hbits d le_rfl hds,
      lateBitWord_congr (s := s) (C := C) (C' := C') (d + 1)
        (fun e he hes => hbits e (by omega) hes)]
  · rw [lateBitWord_eq_nil (by omega), lateBitWord_eq_nil (by omega)]
termination_by s - d
decreasing_by omega

theorem lateBitWord_length (s C d : ℕ) :
    (lateBitWord s C d).length = s - d := by
  by_cases hds : d < s
  · rw [lateBitWord_eq_cons hds, List.length_cons,
      lateBitWord_length s C (d + 1)]
    omega
  · rw [lateBitWord_eq_nil (by omega)]
    simp
    omega
termination_by s - d
decreasing_by omega

theorem lateBitWord_getElem?
    {s C d e : ℕ} (hde : d ≤ e) (hes : e < s) :
    (lateBitWord s C d)[e - d]? = some (Nat.testBit C (2 * s - e)) := by
  by_cases hd : d = e
  · subst hd
    rw [lateBitWord_eq_cons (by omega), Nat.sub_self]
    simp
  · have hlt : d < e := by omega
    have hds : d < s := by omega
    have hstep : e - d = (e - (d + 1)) + 1 := by omega
    rw [lateBitWord_eq_cons hds, hstep, List.getElem?_cons_succ,
      lateBitWord_getElem? (s := s) (C := C) (d := d + 1) (e := e)
        (by omega) hes]
termination_by e - d
decreasing_by omega

/-! ## The correspondence -/

/-- **The late-zone greedy word is the binary expansion of the entering
capacity.**

In the late zone `2 * s < 3 * d` the descending integer greedy run over the
actual truncated Mersenne weights `seamWeightsFrom s d`, started at capacity
`C`, takes rank `e` exactly when bit `2 * s - e` of `C` is set — for every `e`
in `[d, s)` at once, and reading the bits of the *entering* capacity `C`, not of
any running remainder.

The two hypotheses are: `C` does not overflow past bit `2 * s - d` (there are no
larger weights left in the list to absorb it), and the low `s + 1` bits of `C`
can pay for the entire `4 ^ k` correction budget, which is exactly what rules
out a borrow into the compared bits. -/
theorem integerGreedyBits_seamWeightsFrom_eq_lateBitWord
    {s d C : ℕ} (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ C % 2 ^ (s + 1)) :
    integerGreedyBits (seamWeightsFrom s d) C = lateBitWord s C d := by
  by_cases hds : d < s
  · have hd2 : 2 ≤ d := by omega
    have hn : s + 1 ≤ 2 * s - d := by omega
    have hexp : 2 * s - (d + 1) + 1 = 2 * s - d := by omega
    have hpow : (2 : ℕ) ^ (2 * s - d + 1) = 2 ^ (2 * s - d) * 2 := by
      rw [pow_succ]
    have hw :=
      truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank hd2 hds hlate
    have hmodmod : C % 2 ^ (2 * s - d) % 2 ^ (s + 1) = C % 2 ^ (s + 1) :=
      Nat.mod_mod_of_dvd C (pow_dvd_pow 2 hn)
    have hmodlt : C % 2 ^ (2 * s - d) < 2 ^ (2 * s - d) :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    have hcorr := lateCorrection_eq_cons (s := s) (d := d) hds
    rw [seamWeightsFrom_eq_cons hds, lateBitWord_eq_cons hds, hw]
    by_cases htb : Nat.testBit C (2 * s - d) = true
    · -- the bit is set: the greedy takes rank `d`
      have hge2 : 2 ^ (2 * s - d) ≤ C := Nat.ge_two_pow_of_testBit htb
      have hsplit : C = 2 ^ (2 * s - d) + C % 2 ^ (2 * s - d) := by
        rw [Nat.mod_eq_sub_mod hge2, Nat.mod_eq_of_lt (by omega)]
        omega
      have hmodle : C % 2 ^ (s + 1) ≤ C % 2 ^ (2 * s - d) := by
        rw [← hmodmod]
        exact Nat.mod_le _ _
      have h4m : 4 ^ (s - d) ≤ C % 2 ^ (2 * s - d) % 2 ^ (s + 1) := by
        rw [hmodmod]
        omega
      have hge : 4 ^ (s - d) + lateCorrection s (d + 1) ≤
          C % 2 ^ (2 * s - d) := by omega
      simp only [integerGreedyBits]
      rw [if_pos (by omega), htb]
      have hCval : C - (2 ^ (2 * s - d) + 4 ^ (s - d)) =
          C % 2 ^ (2 * s - d) - 4 ^ (s - d) := by omega
      have hnewmod :
          (C % 2 ^ (2 * s - d) - 4 ^ (s - d)) % 2 ^ (s + 1) =
            C % 2 ^ (s + 1) - 4 ^ (s - d) := by
        rw [mod_sub_of_le_mod (Nat.two_pow_pos _) h4m, hmodmod]
      have hrec :=
        integerGreedyBits_seamWeightsFrom_eq_lateBitWord
          (s := s) (d := d + 1) (C := C % 2 ^ (2 * s - d) - 4 ^ (s - d))
          (by omega)
          (by rw [hexp]; exact lt_of_le_of_lt (Nat.sub_le _ _) hmodlt)
          (by rw [hnewmod]; omega)
      have hbits : ∀ e : ℕ, d + 1 ≤ e → e < s →
          Nat.testBit (C % 2 ^ (2 * s - d) - 4 ^ (s - d)) (2 * s - e) =
            Nat.testBit C (2 * s - e) := by
        intro e he hes
        have hj1 : s + 1 ≤ 2 * s - e := by omega
        have hj2 : 2 * s - e < 2 * s - d := by omega
        rw [testBit_sub_of_le_mod h4m hj1]
        simp [Nat.testBit_mod_two_pow, hj2]
      rw [hCval, hrec, lateBitWord_congr (d + 1) hbits]
    · -- the bit is clear: the greedy skips rank `d`
      have htbf : Nat.testBit C (2 * s - d) = false := by
        simpa using htb
      have hClt : C < 2 ^ (2 * s - d) := by
        by_contra hcon
        rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
          (by omega) (by omega)] at htbf
        exact Bool.noConfusion htbf
      have hpos : 0 < (4 : ℕ) ^ (s - d) := by positivity
      simp only [integerGreedyBits]
      rw [if_neg (by omega), htbf]
      have hrec :=
        integerGreedyBits_seamWeightsFrom_eq_lateBitWord
          (s := s) (d := d + 1) (C := C)
          (by omega) (by rw [hexp]; omega)
          (le_trans (lateCorrection_succ_le s d) hlow)
      rw [hrec]
  · rw [seamWeightsFrom_eq_nil (by omega), lateBitWord_eq_nil (by omega)]
    rfl
termination_by s - d
decreasing_by all_goals omega

/-! ## Pointwise form -/

/-- Position `e - d` of the late greedy word is bit `2 * s - e` of `C`. -/
theorem getElem?_eq_testBit
    {s d C e : ℕ} (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ C % 2 ^ (s + 1))
    (hde : d ≤ e) (hes : e < s) :
    (integerGreedyBits (seamWeightsFrom s d) C)[e - d]? =
      some (Nat.testBit C (2 * s - e)) := by
  rw [integerGreedyBits_seamWeightsFrom_eq_lateBitWord hlate hhigh hlow]
  exact lateBitWord_getElem? hde hes

/-- **Take/skip at a single late rank.**  The greedy takes rank `e` iff bit
`2 * s - e` of the entering capacity is one. -/
theorem takes_iff_testBit
    {s d C e : ℕ} (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ C % 2 ^ (s + 1))
    (hde : d ≤ e) (hes : e < s) :
    (integerGreedyBits (seamWeightsFrom s d) C)[e - d]? = some true ↔
      Nat.testBit C (2 * s - e) = true := by
  rw [getElem?_eq_testBit hlate hhigh hlow hde hes]
  simp

/-- **The forced run.**  The greedy takes every late rank iff every bit of `C`
in the window `(s, 2 * s - d]` is one.  Contrapositively: a single zero bit in
that window is a skipped late rank. -/
theorem all_true_iff_forall_testBit
    {s d C : ℕ} (hlate : 2 * s < 3 * d)
    (hhigh : C < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ C % 2 ^ (s + 1)) :
    (∀ e : ℕ, d ≤ e → e < s →
        (integerGreedyBits (seamWeightsFrom s d) C)[e - d]? = some true) ↔
      (∀ e : ℕ, d ≤ e → e < s → Nat.testBit C (2 * s - e) = true) := by
  constructor
  · intro h e hde hes
    exact (takes_iff_testBit hlate hhigh hlow hde hes).mp (h e hde hes)
  · intro h e hde hes
    exact (takes_iff_testBit hlate hhigh hlow hde hes).mpr (h e hde hes)

/-! ## The actual seam greedy run, split at the first late rank -/

/-- Descending greedy over a concatenation runs the prefix first and then feeds
its remainder to the suffix. -/
theorem integerGreedyBits_append (l₁ l₂ : List ℕ) (C : ℕ) :
    integerGreedyBits (l₁ ++ l₂) C =
      integerGreedyBits l₁ C ++
        integerGreedyBits l₂ (C - weightedBoolSum l₁ (integerGreedyBits l₁ C)) := by
  induction l₁ generalizing C with
  | nil => simp [integerGreedyBits, weightedBoolSum]
  | cons w ws ih =>
      rw [List.cons_append]
      by_cases hw : w ≤ C
      · rw [integerGreedyBits, if_pos hw, integerGreedyBits, if_pos hw,
          List.cons_append, ih (C - w)]
        change _ = _ :: (_ ++ integerGreedyBits l₂
          (C - (w + weightedBoolSum ws (integerGreedyBits ws (C - w)))))
        rw [← Nat.sub_sub]
      · rw [integerGreedyBits, if_neg hw, integerGreedyBits, if_neg hw,
          List.cons_append, ih C]
        rfl

theorem seamWeightsFrom_drop (s : ℕ) :
    ∀ (k d : ℕ), (seamWeightsFrom s d).drop k = seamWeightsFrom s (d + k) := by
  intro k
  induction k with
  | zero => intro d; simp
  | succ k ih =>
      intro d
      by_cases h : d < s
      · rw [seamWeightsFrom_eq_cons h, List.drop_succ_cons, ih (d + 1)]
        congr 1
        omega
      · rw [seamWeightsFrom_eq_nil (by omega), List.drop_nil,
          seamWeightsFrom_eq_nil (by omega)]

theorem seamWeights_eq_take_append {s d : ℕ} (h2 : 2 ≤ d) :
    seamWeights s = (seamWeights s).take (d - 2) ++ seamWeightsFrom s d := by
  conv_lhs => rw [← List.take_append_drop (d - 2) (seamWeights s)]
  congr 1
  unfold seamWeights
  rw [seamWeightsFrom_drop]
  congr 1
  omega

/-- The seam weights strictly before the late zone. -/
def earlyWeights (s d : ℕ) : List ℕ := (seamWeights s).take (d - 2)

theorem earlyWeights_length {s d : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s) :
    (earlyWeights s d).length = d - 2 := by
  unfold earlyWeights
  rw [List.length_take, seamWeights_length_eq]
  omega

/-- **The remainder entering the late zone**: what the actual seam greedy run
has left after processing ranks `2, …, d-1`. -/
def lateEntryRemainder (s d : ℕ) : ℕ :=
  seamSubsetTarget s -
    weightedBoolSum (earlyWeights s d)
      (integerGreedyBits (earlyWeights s d) (seamSubsetTarget s))

theorem seamGreedyBits_split {s d : ℕ} (h2 : 2 ≤ d) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
      integerGreedyBits (earlyWeights s d) (seamSubsetTarget s) ++
        integerGreedyBits (seamWeightsFrom s d) (lateEntryRemainder s d) := by
  conv_lhs => rw [seamWeights_eq_take_append h2]
  rw [integerGreedyBits_append]
  rfl

theorem mem_seamGreedySupport_iff_getElem
    {s e : ℕ} (h2 : 2 ≤ e) (hes : e < s) :
    e ∈ seamWordSupport (seamGreedyWord s) ↔
      (integerGreedyBits (seamWeights s) (seamSubsetTarget s))[e - 2]? =
        some true := by
  classical
  have hlen :
      (integerGreedyBits (seamWeights s) (seamSubsetTarget s)).length = s - 2 := by
    rw [integerGreedyBits_length, seamWeights_length_eq]
  have hidx :
      e - 2 < (integerGreedyBits (seamWeights s) (seamSubsetTarget s)).length := by
    rw [hlen]
    omega
  rw [List.getElem?_eq_getElem hidx]
  constructor
  · rintro hmem
    obtain ⟨i, hi, hei⟩ := mem_seamWordSupport_iff.mp hmem
    have hiv : (i : ℕ) = e - 2 := by omega
    simp only [seamGreedyWord, SeamRowWord.ofList] at hi
    simp only [Option.some.injEq]
    rw [← hi]
    congr 1
    omega
  · intro hb
    apply mem_seamWordSupport_iff.mpr
    refine ⟨⟨e - 2, by omega⟩, ?_, show e = (e - 2) + 2 by omega⟩
    simp only [seamGreedyWord, SeamRowWord.ofList]
    simp only [Option.some.injEq] at hb
    rw [← hb]
    congr 1

/-- **Bit criterion for the corpus's own seam greedy word.**  Once the entering
remainder `lateEntryRemainder s d` satisfies the two side conditions, membership
of a late rank `e` in `seamWordSupport (seamGreedyWord s)` is *exactly* bit
`2 * s - e` of that remainder. -/
theorem mem_seamGreedySupport_iff_testBit
    {s d e : ℕ} (h2 : 2 ≤ d) (hds : d ≤ s) (hlate : 2 * s < 3 * d)
    (hhigh : lateEntryRemainder s d < 2 ^ (2 * s - d + 1))
    (hlow : lateCorrection s d ≤ lateEntryRemainder s d % 2 ^ (s + 1))
    (hde : d ≤ e) (hes : e < s) :
    e ∈ seamWordSupport (seamGreedyWord s) ↔
      Nat.testBit (lateEntryRemainder s d) (2 * s - e) = true := by
  have hlenE :
      (integerGreedyBits (earlyWeights s d) (seamSubsetTarget s)).length = d - 2 := by
    rw [integerGreedyBits_length, earlyWeights_length h2 hds]
  rw [mem_seamGreedySupport_iff_getElem (by omega) hes, seamGreedyBits_split h2,
    List.getElem?_append_right (by rw [hlenE]; omega), hlenE,
    show e - 2 - (d - 2) = e - d by omega,
    getElem?_eq_testBit hlate hhigh hlow hde hes]
  simp

/-! ## Concrete instance: `s = 20`, late zone starting at `d = 14` -/

namespace Concrete

/-- `14` really is the first late rank at `s = 20`. -/
theorem fourteen_is_first_late : 2 * 20 < 3 * 14 ∧ ¬ (2 * 20 < 3 * 13) := by
  refine ⟨by norm_num, by norm_num⟩

/-- The six late weights at `s = 20`: ranks `14, …, 19`, computed from the
corpus definition `truncatedMersenneWeight s d = 4 ^ s / (2 ^ d - 1)`. -/
theorem seamWeightsFrom_twenty_fourteen :
    seamWeightsFrom 20 14 =
      [67112960, 33555456, 16777472, 8388672, 4194320, 2097156] := by
  rw [seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight]
  decide +kernel

theorem lateCorrection_twenty_fourteen : lateCorrection 20 14 = 5460 := by
  rw [lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_zero (by norm_num)]
  decide +kernel

/-- **The hypotheses of the main theorem are satisfiable.**  This is the
anti-vacuity certificate. -/
theorem hypotheses_hold :
    2 * 20 < 3 * 14 ∧
      (87217799 : ℕ) < 2 ^ (2 * 20 - 14 + 1) ∧
        lateCorrection 20 14 ≤ 87217799 % 2 ^ (20 + 1) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [lateCorrection_twenty_fourteen]
  decide +kernel

/-- The greedy word, computed from the actual truncated Mersenne weights. -/
theorem greedy_word :
    integerGreedyBits (seamWeightsFrom 20 14) 87217799 =
      [true, false, true, false, false, true] := by
  rw [seamWeightsFrom_twenty_fourteen]
  decide +kernel

/-- The bit word, computed from the binary expansion of the capacity. -/
theorem bit_word :
    lateBitWord 20 87217799 14 = [true, false, true, false, false, true] := by
  rw [lateBitWord_eq_cons (by norm_num), lateBitWord_eq_cons (by norm_num),
    lateBitWord_eq_cons (by norm_num), lateBitWord_eq_cons (by norm_num),
    lateBitWord_eq_cons (by norm_num), lateBitWord_eq_cons (by norm_num),
    lateBitWord_eq_nil (by norm_num)]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- The main theorem, instantiated: hypotheses verified, and the conclusion
verified independently on both sides. -/
theorem correspondence :
    integerGreedyBits (seamWeightsFrom 20 14) 87217799 =
      lateBitWord 20 87217799 14 := by
  refine integerGreedyBits_seamWeightsFrom_eq_lateBitWord
    (by norm_num) (by norm_num) ?_
  rw [lateCorrection_twenty_fourteen]
  decide +kernel

/-! ### The *actual* seam remainder at `s = 20`

Everything above uses an arbitrary admissible capacity.  The real payoff is that
the genuine remainder produced by the corpus's own greedy run at `s = 20`
satisfies the side conditions too, so the correspondence is not merely
satisfiable but applies to the object of Erdős #257. -/

/-- The eighteen seam weights at `s = 20`, from the corpus definition. -/
theorem seamWeights_twenty :
    seamWeights 20 =
      [366503875925, 157073089682, 73300775185, 35468117025, 17452565520,
        8657571872, 4311810305, 2151686160, 1074791425, 537133184, 268501008,
        134234114, 67112960, 33555456, 16777472, 8388672, 4194320, 2097156] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight]
  decide +kernel

/-- The genuine remainder entering the late zone at `s = 20`. -/
theorem lateEntryRemainder_twenty_fourteen :
    lateEntryRemainder 20 14 = 67662313 := by
  unfold lateEntryRemainder earlyWeights
  rw [seamWeights_twenty]
  simp only [seamSubsetTarget]
  decide +kernel

/-- **The side conditions hold for the actual seam remainder.** -/
theorem actual_hypotheses_hold :
    lateEntryRemainder 20 14 < 2 ^ (2 * 20 - 14 + 1) ∧
      lateCorrection 20 14 ≤ lateEntryRemainder 20 14 % 2 ^ (20 + 1) := by
  rw [lateEntryRemainder_twenty_fourteen, lateCorrection_twenty_fourteen]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The actual late greedy word at `s = 20`: rank `14` is taken, ranks
`15, …, 19` are all skipped. -/
theorem actual_late_word :
    integerGreedyBits (seamWeightsFrom 20 14) (lateEntryRemainder 20 14) =
      [true, false, false, false, false, false] := by
  rw [lateEntryRemainder_twenty_fourteen, seamWeightsFrom_twenty_fourteen]
  decide +kernel

theorem fourteen_mem_seamGreedySupport_twenty :
    14 ∈ seamWordSupport (seamGreedyWord 20) := by
  rw [mem_seamGreedySupport_iff_testBit (d := 14) (by norm_num) (by norm_num)
      (by norm_num) actual_hypotheses_hold.1 actual_hypotheses_hold.2
      (by norm_num) (by norm_num),
    lateEntryRemainder_twenty_fourteen]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- **A genuine skipped late rank at `s = 20`**, read straight off a zero bit of
the entering remainder.  Since `2 * 20 < 3 * 15`, rank `15` is in the late zone;
this is exactly the input of `SkipD3.largestSkipLateAt_of_late_skip`. -/
theorem fifteen_not_mem_seamGreedySupport_twenty :
    15 ∉ seamWordSupport (seamGreedyWord 20) := by
  rw [mem_seamGreedySupport_iff_testBit (d := 14) (by norm_num) (by norm_num)
      (by norm_num) actual_hypotheses_hold.1 actual_hypotheses_hold.2
      (by norm_num) (by norm_num),
    lateEntryRemainder_twenty_fourteen]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

theorem fifteen_is_late : 2 * 20 < 3 * 15 := by norm_num

theorem nineteen_not_mem_seamGreedySupport_twenty :
    19 ∉ seamWordSupport (seamGreedyWord 20) := by
  rw [mem_seamGreedySupport_iff_testBit (d := 14) (by norm_num) (by norm_num)
      (by norm_num) actual_hypotheses_hold.1 actual_hypotheses_hold.2
      (by norm_num) (by norm_num),
    lateEntryRemainder_twenty_fourteen]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- **The bit criterion delivers the corpus predicate.**  Rank `19` is the
largest false rank of row `20` and it is late, so `LargestSkipLateAt 20` — the
property whose cofinality is equivalent to `1/2 ∈ mersenneAchievementSet` —
holds, proved here purely from a zero bit of the entering remainder. -/
theorem largestSkipLateAt_twenty : LargestSkipLateAt 20 :=
  ⟨19, ⟨by norm_num, by norm_num, nineteen_not_mem_seamGreedySupport_twenty,
      fun e h1 h2 => absurd h2 (by omega)⟩, by norm_num⟩

end Concrete

end BitCorr

end Erdos249257
