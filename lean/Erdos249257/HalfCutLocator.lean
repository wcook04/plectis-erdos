import Erdos249257.GreedyAchievementSet

/-!
# Half cut locator: straddle prefixes, rank-step forcing, and fatal gaps

This module lands the theorem-grade core of the Packet 4 graph-transform
return.  The target `1/2` defines a Dedekind cut in the superincreasing
Mersenne coding; the graph transform is a cut locator, not a contraction.
The landed content is:

* the one-bit-optimal correction-tail window `2^{-(2m+2)} < η_m < 2^{-(2m+1)}`
  (packet §3), together with the exact jump identity `g_m = c_m - η_m` and
  uniqueness of a dyadic boundary of depth `2m+1` inside a correction window
  (packet §5);
* the *search-cylinder straddle* invariant `W(u) ≤ t ≤ W(u) + τ_d`, kept
  deliberately weaker than the `HalfPrefixForcingChain` containment field
  (packet §4);
* the closed-set straddle criterion: straddling finite prefixes at every
  depth already force membership.  Because `mersenneAchievementSet` is
  compact, no nested-chain or coinductive interface is required — this is
  strictly stronger than the packet's §8 composition, which assumed nested
  cylinders;
* the rank-step trichotomy: a straddling prefix either still straddles after
  skipping the next exponent, straddles after selecting it, or exposes a
  fatal Mersenne gap (packet (23) in rank-granular form);
* for the half target both boundary equalities are impossible — the greedy
  endpoint `r = w_j` by odd reduced denominators, the lazy endpoint
  `r = τ_j` by Erdős–Borwein irrationality — so the half-specialized step is
  the strict `refined | fatal` dichotomy of packet (25);
* the fatal-gap exclusion theorem: a rank gap excludes *every* support
  sharing the finite prefix, not only the greedy orbit (packet (24));
* the global mechanism dichotomy of packet (29): either some finite prefix
  certifies a fatal gap, or `1/2 ∈ mersenneAchievementSet`;
* the exact regression fixtures `1/2 - W({2,3,6,7}) = 1/16002`,
  `η_1 ≤ 5/42`, and `3/8 < 1/2 - η_1` (packet §9).

What is *not* claimed: which branch of the dichotomy the half target takes.
Deciding that the fatal branch never occurs is exactly Erdős #257 for `1/2`
and remains open.  The binary-cell five-way boundary classifier and the
`m ↦ 2m+1` constructive evaluator stay advisory; the rank-granular step
proved here is finer and subsumes their arithmetic content.

No novelty or priority claim is made for the theorems in this file.
-/

namespace Erdos249257

open Filter Set Topology

/-! ## One-bit-optimal correction-tail window -/

/-- **Packet §3 upper constant.**  The unresolved correction after `m` is
strictly below one half of the binary cell `4^{-m}`: the sharp uniform
window depth is `2m+1`. -/
theorem mersenneCorrectionTail_lt_doubleDepth {m : ℕ} (hm : 0 < m) :
    mersenneCorrectionTail m < ((1 : ℝ) / 2) ^ (2 * m + 1) := by
  have hle := mersenneCorrectionTail_le m
  have h8 : ((1 : ℝ) / 8) ^ m = ((1 : ℝ) / 2) ^ m * ((1 : ℝ) / 4) ^ m := by
    rw [← mul_pow]
    norm_num
  have hhalf : ((1 : ℝ) / 2) ^ m ≤ (1 : ℝ) / 2 := by
    calc
      ((1 : ℝ) / 2) ^ m ≤ ((1 : ℝ) / 2) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = (1 : ℝ) / 2 := pow_one _
  have hq : (0 : ℝ) < ((1 : ℝ) / 4) ^ m := by positivity
  have hgoal : ((1 : ℝ) / 2) ^ (2 * m + 1)
      = ((1 : ℝ) / 2) * ((1 : ℝ) / 4) ^ m := by
    have h4 : ((1 : ℝ) / 2) ^ 2 = (1 : ℝ) / 4 := by norm_num
    rw [pow_succ, pow_mul, h4]
    ring
  have h8le : ((1 : ℝ) / 8) ^ m ≤ ((1 : ℝ) / 2) * ((1 : ℝ) / 4) ^ m := by
    rw [h8]
    exact mul_le_mul_of_nonneg_right hhalf hq.le
  rw [hgoal]
  nlinarith

/-- **Packet §3 lower constant.**  The correction tail strictly exceeds the
quarter cell, so no uniform tail-width argument can promise depth `2m+2`. -/
theorem doubleDepth_succ_lt_mersenneCorrectionTail (m : ℕ) :
    ((1 : ℝ) / 2) ^ (2 * m + 2) < mersenneCorrectionTail m := by
  have heq := mersenneCorrectionTail_eq m
  have hrem := mersenneWeightRemainderTail_pos m
  have hq : (0 : ℝ) < ((1 : ℝ) / 4) ^ m := by positivity
  have hgoal : ((1 : ℝ) / 2) ^ (2 * m + 2)
      = ((1 : ℝ) / 4) * ((1 : ℝ) / 4) ^ m := by
    have h4 : ((1 : ℝ) / 2) ^ 2 = (1 : ℝ) / 4 := by norm_num
    rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, h4, pow_succ]
    ring
  rw [heq, hgoal]
  nlinarith

/-- **Packet §2 jump identity.**  The Mersenne gap is exactly the one-weight
correction minus the correction tail: `g_m = c_m - η_m`. -/
theorem mersenneGap_eq_weightCorrection_sub_correctionTail (n : ℕ) :
    mersenneGap n
      = (mersenneWeight n - ((1 : ℝ) / 2) ^ n) - mersenneCorrectionTail n := by
  unfold mersenneGap mersenneCorrectionTail
  ring

/-- **Packet §5 boundary uniqueness.**  A correction window of width `η_m`
meets at most one dyadic boundary of depth `2m+1`: the two candidate
numerators coincide.  This is the quadratic cut-localisation step. -/
theorem correctionWindow_dyadic_crossing_unique {m : ℕ} (hm : 0 < m)
    {x : ℝ} {k₁ k₂ : ℤ}
    (h₁L : x < (k₁ : ℝ) / 2 ^ (2 * m + 1))
    (h₁R : (k₁ : ℝ) / 2 ^ (2 * m + 1) < x + mersenneCorrectionTail m)
    (h₂L : x < (k₂ : ℝ) / 2 ^ (2 * m + 1))
    (h₂R : (k₂ : ℝ) / 2 ^ (2 * m + 1) < x + mersenneCorrectionTail m) :
    k₁ = k₂ := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (2 * m + 1) := by positivity
  have hone : ((1 : ℝ) / 2) ^ (2 * m + 1) * (2 : ℝ) ^ (2 * m + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hτ : mersenneCorrectionTail m * (2 : ℝ) ^ (2 * m + 1) ≤ 1 := by
    have hlt := mersenneCorrectionTail_lt_doubleDepth hm
    nlinarith
  have e₁ : ((k₁ : ℝ) / 2 ^ (2 * m + 1)) * (2 : ℝ) ^ (2 * m + 1) = (k₁ : ℝ) :=
    div_mul_cancel₀ _ hpow.ne'
  have e₂ : ((k₂ : ℝ) / 2 ^ (2 * m + 1)) * (2 : ℝ) ^ (2 * m + 1) = (k₂ : ℝ) :=
    div_mul_cancel₀ _ hpow.ne'
  have h₁L' := mul_lt_mul_of_pos_right h₁L hpow
  rw [e₁] at h₁L'
  have h₁R' := mul_lt_mul_of_pos_right h₁R hpow
  rw [e₁, add_mul] at h₁R'
  have h₂L' := mul_lt_mul_of_pos_right h₂L hpow
  rw [e₂] at h₂L'
  have h₂R' := mul_lt_mul_of_pos_right h₂R hpow
  rw [e₂, add_mul] at h₂R'
  exact integer_crossing_unique hτ h₁L' h₁R' h₂L' h₂R'

/-! ## Finite support words -/

/-- The value coded by a finite positive support is its literal finite
Mersenne sum. -/
theorem positiveMersenneSupportValue_coe_finset (F : Finset ℕ) :
    positiveMersenneSupportValue (↑F : Set ℕ) = ∑ n ∈ F, mersenneWeight n := by
  rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
  unfold finiteErdosSum
  push_cast
  exact Finset.sum_congr rfl fun n _ => by rw [mersenneWeight]

/-- Selecting one new exponent adds exactly its weight. -/
theorem positiveMersenneSupportValue_insert {F : Finset ℕ} {a : ℕ}
    (ha : a ∉ F) :
    positiveMersenneSupportValue (↑(insert a F) : Set ℕ)
      = mersenneWeight a + positiveMersenneSupportValue (↑F : Set ℕ) := by
  rw [positiveMersenneSupportValue_coe_finset,
    positiveMersenneSupportValue_coe_finset, Finset.sum_insert ha]

/-! ## Search-cylinder straddle invariant -/

/-- **Packet §4.**  A finite support word certified to straddle the target at
depth `d`: the coded value is at most `t` and the value plus the complete
unresolved tail mass still reaches `t`.  This is deliberately *weaker* than
the `HalfPrefixForcingChain.interval_trapped` containment condition: overlap
of the correction image with the cylinder, not containment inside it. -/
structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d

/-- Zero is never an exponent of a straddle word. -/
theorem IsStraddlePrefix.zero_notMem {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix t u d) : 0 ∉ u :=
  fun h => absurd (hu.mem_bounds 0 h).1 (lt_irrefl 0)

/-- **Closed-set straddle criterion.**  If some finite word straddles the
target at every depth, the target is achieved.  Compactness of the
achievement set replaces the packet's nested-cylinder limit: the straddle
words need not be nested, consistent, or produced by any common process. -/
theorem mem_mersenneAchievementSet_of_straddle_all_depths {t : ℝ}
    (h : ∀ d : ℕ, ∃ u : Finset ℕ, IsStraddlePrefix t u d) :
    t ∈ mersenneAchievementSet := by
  choose u hu using h
  have hmem : ∀ d : ℕ,
      positiveMersenneSupportValue (↑(u d) : Set ℕ) ∈ mersenneAchievementSet :=
    fun d => ⟨(↑(u d) : Set ℕ),
      fun h0 => (hu d).zero_notMem (Finset.mem_coe.mp h0), rfl⟩
  have hlow : ∀ d : ℕ,
      t - mersenneTail d ≤ positiveMersenneSupportValue (↑(u d) : Set ℕ) := by
    intro d
    have := (hu d).le_value_add_tail
    linarith
  have hhigh : ∀ d : ℕ,
      positiveMersenneSupportValue (↑(u d) : Set ℕ) ≤ t :=
    fun d => (hu d).value_le
  have htail : Tendsto (fun d : ℕ => t - mersenneTail d) atTop (nhds t) := by
    simpa using tendsto_const_nhds.sub tendsto_mersenneTail_zero
  have hxlim : Tendsto
      (fun d : ℕ => positiveMersenneSupportValue (↑(u d) : Set ℕ))
      atTop (nhds t) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le htail tendsto_const_nhds
      hlow hhigh
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hxlim
    (Filter.Eventually.of_forall hmem)

/-! ## Rank-step trichotomy -/

/-- **Packet (23), rank-granular form.**  From a straddle at depth `d`, one
exact comparison of the residual against `(τ_{d+1}, w_{d+1})` yields: the
word still straddles after skipping `d+1`, the extended word straddles after
selecting `d+1`, or the target sits in the fatal Mersenne gap. -/
theorem isStraddlePrefix_step_trichotomy {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix t u d) :
    IsStraddlePrefix t u (d + 1) ∨
      IsStraddlePrefix t (insert (d + 1) u) (d + 1) ∨
        (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t ∧
          t < positiveMersenneSupportValue (↑u : Set ℕ)
              + mersenneWeight (d + 1)) := by
  have hsplit := mersenneTail_eq_weight_add d
  have hd1 : d + 1 ∉ u := fun hmem => by
    have := (hu.mem_bounds _ hmem).2
    omega
  have hins := positiveMersenneSupportValue_insert (F := u) (a := d + 1) hd1
  by_cases hskip :
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
  · exact Or.inl
      ⟨fun n hn => ⟨(hu.mem_bounds n hn).1,
        (hu.mem_bounds n hn).2.trans (Nat.le_succ d)⟩, hu.value_le, hskip⟩
  · push_neg at hskip
    by_cases htake :
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1) ≤ t
    · refine Or.inr (Or.inl ⟨fun n hn => ?_, ?_, ?_⟩)
      · rcases Finset.mem_insert.mp hn with rfl | hn'
        · exact ⟨Nat.succ_pos d, le_refl _⟩
        · exact ⟨(hu.mem_bounds n hn').1,
            (hu.mem_bounds n hn').2.trans (Nat.le_succ d)⟩
      · rw [hins]
        linarith
      · rw [hins]
        have := hu.le_value_add_tail
        linarith
    · push_neg at htake
      exact Or.inr (Or.inr ⟨hskip, htake⟩)

/-! ## The two boundary equalities are impossible for the half target -/

/-- **Greedy endpoint kill.**  No finite positive support word has value
exactly `1/2`: the audited reduced denominator of the finite Erdős sum is
odd. -/
theorem positiveMersenneSupportValue_coe_finset_ne_half
    {u : Finset ℕ} (h0 : 0 ∉ u) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≠ (1 / 2 : ℝ) := by
  intro hhalf
  have hcast : ((finiteErdosSum u 2 : ℚ) : ℝ) = ((1 / 2 : ℚ) : ℝ) := by
    rw [← positiveMersenneSupportValue_eq_cast_finiteErdosSum, hhalf]
    norm_num
  have hrat : finiteErdosSum u 2 = (1 / 2 : ℚ) :=
    Rat.cast_injective (α := ℝ) hcast
  have hcop := coprime_base_den_finiteErdosSum u 2 h0 (by norm_num)
  rw [hrat] at hcop
  have hden : ((1 : ℚ) / 2).den = 2 := by
    have h := den_natCast_div_natCast 1 2 (by norm_num)
    simpa using h
  rw [hden] at hcop
  exact absurd hcop (by decide)

/-- **Lazy endpoint kill.**  No finite positive support word plus a complete
depth-`d` tail equals `1/2`: otherwise the Erdős–Borwein constant would be
rational. -/
theorem half_ne_coe_finset_add_mersenneTail
    (u : Finset ℕ) (d : ℕ) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
      ≠ (1 / 2 : ℝ) := by
  intro hhalf
  have hprefix : mersennePrefixMass d
      = ((∑ k ∈ Finset.range d, mersenneWeightRat (k + 1) : ℚ) : ℝ) := by
    unfold mersennePrefixMass
    push_cast
    exact Finset.sum_congr rfl fun k _ => (cast_mersenneWeightRat (k + 1)).symm
  apply irrational_erdosBorweinMersenneConstant.ne_rat
    ((∑ k ∈ Finset.range d, mersenneWeightRat (k + 1))
      + ((1 : ℚ) / 2 - finiteErdosSum u 2))
  rw [erdosBorweinMersenneConstant_eq_prefix_add_tail d]
  have htail : mersenneTail d
      = (1 / 2 : ℝ) - positiveMersenneSupportValue (↑u : Set ℕ) := by
    linarith
  rw [htail, hprefix, positiveMersenneSupportValue_eq_cast_finiteErdosSum]
  push_cast
  ring

/-- **Packet §7.**  For the half target every straddle is strictly interior:
both dyadic-expansion endpoint cases of the crossed-boundary classification
are impossible. -/
theorem IsStraddlePrefix.half_strict {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    positiveMersenneSupportValue (↑u : Set ℕ) < 1 / 2 ∧
      (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
        + mersenneTail d := by
  constructor
  · exact lt_of_le_of_ne hu.value_le
      (positiveMersenneSupportValue_coe_finset_ne_half hu.zero_notMem)
  · exact lt_of_le_of_ne hu.le_value_add_tail
      (Ne.symm (half_ne_coe_finset_add_mersenneTail u d))

/-- **Packet (25).**  The half-specialized macrostep is deterministic: from a
straddle at depth `d`, exactly one of skip-refinement, take-refinement, or a
fatal gap occurs, and the two refinement branches exclude each other. -/
theorem IsStraddlePrefix.half_step_forced {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    (IsStraddlePrefix (1 / 2 : ℝ) u (d + 1) ∧
        ¬ IsStraddlePrefix (1 / 2 : ℝ) (insert (d + 1) u) (d + 1)) ∨
      (IsStraddlePrefix (1 / 2 : ℝ) (insert (d + 1) u) (d + 1) ∧
          ¬ IsStraddlePrefix (1 / 2 : ℝ) u (d + 1)) ∨
        (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
            < 1 / 2 ∧
          (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
            + mersenneWeight (d + 1)) := by
  have hd1 : d + 1 ∉ u := fun hmem => by
    have := (hu.mem_bounds _ hmem).2
    omega
  have hins := positiveMersenneSupportValue_insert (F := u) (a := d + 1) hd1
  have hgap := mersenneTail_lt_weight (n := d + 1) (Nat.succ_pos d)
  rcases isStraddlePrefix_step_trichotomy hu with hskip | htake | hfatal
  · refine Or.inl ⟨hskip, fun htake => ?_⟩
    have hstrict := hskip.half_strict
    have hlow := htake.value_le
    rw [hins] at hlow
    linarith [hstrict.2]
  · refine Or.inr (Or.inl ⟨htake, fun hskip => ?_⟩)
    have hstrict := htake.half_strict
    rw [hins] at hstrict
    have hhigh := hskip.le_value_add_tail
    linarith [hstrict.1]
  · exact Or.inr (Or.inr hfatal)

/-! ## Canonicality of the straddling word -/

/-- Removing the top bit from a depth-`d+1` straddling word recovers a
depth-`d` straddling word.  This is the backwards edge needed to compare the
cut-locator tree with the canonical greedy recursion. -/
theorem IsStraddlePrefix.erase_top {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix t u (d + 1)) :
    IsStraddlePrefix t (u.erase (d + 1)) d := by
  have hbounds : ∀ n ∈ u.erase (d + 1), 0 < n ∧ n ≤ d := by
    intro n hn
    have hmem := Finset.mem_of_mem_erase hn
    have hne : n ≠ d + 1 := (Finset.mem_erase.mp hn).1
    have hle : n ≤ d + 1 := (hu.mem_bounds n hmem).2
    have hlt : n < d + 1 := lt_of_le_of_ne hle hne
    exact ⟨(hu.mem_bounds n hmem).1, Nat.lt_succ_iff.mp hlt⟩
  have htail := mersenneTail_eq_weight_add d
  by_cases htop : d + 1 ∈ u
  · have hnot : d + 1 ∉ u.erase (d + 1) := Finset.notMem_erase _ _
    have hvalue :
        positiveMersenneSupportValue (↑u : Set ℕ) =
          mersenneWeight (d + 1) +
            positiveMersenneSupportValue (↑(u.erase (d + 1)) : Set ℕ) := by
      calc
        positiveMersenneSupportValue (↑u : Set ℕ) =
            positiveMersenneSupportValue
              (↑(insert (d + 1) (u.erase (d + 1))) : Set ℕ) :=
          congrArg
            (fun v : Finset ℕ =>
              positiveMersenneSupportValue (↑v : Set ℕ))
            (Finset.insert_erase htop).symm
        _ = mersenneWeight (d + 1) +
              positiveMersenneSupportValue
                (↑(u.erase (d + 1)) : Set ℕ) :=
          positiveMersenneSupportValue_insert hnot
    refine ⟨hbounds, ?_, ?_⟩
    · have hweight := mersenneWeight_pos (Nat.succ_pos d)
      linarith [hu.value_le, hvalue]
    · linarith [hu.le_value_add_tail, hvalue]
  · have herase : u.erase (d + 1) = u := Finset.erase_eq_of_notMem htop
    refine ⟨hbounds, ?_, ?_⟩
    · have hweight := mersenneWeight_pos (Nat.succ_pos d)
      simpa [herase] using hu.value_le
    · rw [herase]
      have hweight := mersenneWeight_pos (Nat.succ_pos d)
      linarith [hu.le_value_add_tail]

/-! ## Fatal gaps exclude every extension -/

/-- **Packet (24), general form.**  If the target sits strictly inside the
rank-`(d+1)` Mersenne gap over the prefix mass of `A` through `d`, then the
support `A` does not achieve the target — whichever way it continues. -/
theorem positiveMersenneSupportValue_ne_of_rank_gap {t : ℝ} {A : Set ℕ}
    {d : ℕ}
    (hlo : mersenneSupportPrefix A d + mersenneTail (d + 1) < t)
    (hhi : t < mersenneSupportPrefix A d + mersenneWeight (d + 1)) :
    positiveMersenneSupportValue A ≠ t := by
  intro hval
  have hsplit : positiveMersenneSupportValue A
      = mersenneSupportPrefix A d + positiveMersenneSupportSuffix A d := by
    unfold mersenneSupportPrefix
    exact positiveMersenneSupportValue_eq_prefix_add_suffix A d
  have hrec := positiveMersenneSupportSuffix_eq_indicator_add A d
  have hsuffnn := positiveMersenneSupportSuffix_nonneg A (d + 1)
  have hsuffle := positiveMersenneSupportSuffix_le_tail A (d + 1)
  by_cases hmem : d + 1 ∈ A
  · rw [Set.indicator_of_mem hmem] at hrec
    linarith
  · rw [Set.indicator_of_notMem hmem, zero_add] at hrec
    linarith

/-- Prefix agreement transports a finite word's value onto the support
prefix mass. -/
theorem mersenneSupportPrefix_eq_coe_finset {A : Set ℕ} {u : Finset ℕ}
    {d : ℕ} (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u)) :
    mersenneSupportPrefix A d = positiveMersenneSupportValue (↑u : Set ℕ) := by
  have hterm : ∀ k ∈ Finset.range d,
      Set.indicator A mersenneWeight (k + 1)
        = if k + 1 ∈ u then mersenneWeight (k + 1) else 0 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    by_cases hku : k + 1 ∈ u
    · rw [if_pos hku,
        Set.indicator_of_mem ((hagree (k + 1) (by omega) (by omega)).mpr hku)]
    · rw [if_neg hku, Set.indicator_of_notMem
        (fun hA => hku ((hagree (k + 1) (by omega) (by omega)).mp hA))]
  have himg : u = Finset.image (fun k => k + 1)
      ((Finset.range d).filter (fun k => k + 1 ∈ u)) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hn
      obtain ⟨hpos, hle⟩ := hu n hn
      exact ⟨n - 1, ⟨by omega, by rwa [Nat.sub_add_cancel hpos]⟩,
        Nat.sub_add_cancel hpos⟩
    · rintro ⟨k, ⟨-, hk⟩, rfl⟩
      exact hk
  rw [positiveMersenneSupportValue_coe_finset]
  unfold mersenneSupportPrefix
  calc
    ∑ k ∈ Finset.range d, Set.indicator A mersenneWeight (k + 1)
        = ∑ k ∈ Finset.range d,
            (if k + 1 ∈ u then mersenneWeight (k + 1) else 0) :=
          Finset.sum_congr rfl hterm
    _ = ∑ k ∈ (Finset.range d).filter (fun k => k + 1 ∈ u),
            mersenneWeight (k + 1) := (Finset.sum_filter _ _).symm
    _ = ∑ n ∈ u, mersenneWeight n := by
          conv_rhs => rw [himg]
          rw [Finset.sum_image (fun x _ y _ h => by omega)]

/-- Every half-straddling word is the actual greedy word through the same
depth.  Strict superincreasingness enters only in the skipped top-bit case;
the selected case follows from the prefix being below the target. -/
theorem IsStraddlePrefix.half_agrees_greedy
    {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    ∀ n : ℕ, 0 < n → n ≤ d →
      (n ∈ u ↔ n ∈ greedyMersenneSupport (1 / 2 : ℝ)) := by
  induction d generalizing u with
  | zero =>
      intro n hn hnd
      omega
  | succ d ih =>
      have hparent := hu.erase_top
      have hagreeParent := ih hparent
      intro n hn hnd
      by_cases htopIndex : n = d + 1
      · subst n
        have hprefix :
            mersenneSupportPrefix
                (greedyMersenneSupport (1 / 2 : ℝ)) d =
              positiveMersenneSupportValue
                (↑(u.erase (d + 1)) : Set ℕ) :=
          mersenneSupportPrefix_eq_coe_finset hparent.mem_bounds
            (fun m hm hmd => (hagreeParent m hm hmd).symm)
        have hgreedy :=
          greedyMersenne_prefix_add_remainder (1 / 2 : ℝ) d
        change (1 / 2 : ℝ) =
            mersenneSupportPrefix
                (greedyMersenneSupport (1 / 2 : ℝ)) d +
              greedyMersenneRemainder (1 / 2 : ℝ) d at hgreedy
        by_cases htopMem : d + 1 ∈ u
        · constructor
          · intro _
            rw [succ_mem_greedyMersenneSupport_iff]
            have hnot : d + 1 ∉ u.erase (d + 1) :=
              Finset.notMem_erase _ _
            have hvalue :
                positiveMersenneSupportValue (↑u : Set ℕ) =
                  mersenneWeight (d + 1) +
                    positiveMersenneSupportValue
                      (↑(u.erase (d + 1)) : Set ℕ) := by
              calc
                positiveMersenneSupportValue (↑u : Set ℕ) =
                    positiveMersenneSupportValue
                      (↑(insert (d + 1) (u.erase (d + 1))) : Set ℕ) :=
                  congrArg
                    (fun v : Finset ℕ =>
                      positiveMersenneSupportValue (↑v : Set ℕ))
                    (Finset.insert_erase htopMem).symm
                _ = mersenneWeight (d + 1) +
                      positiveMersenneSupportValue
                        (↑(u.erase (d + 1)) : Set ℕ) :=
                  positiveMersenneSupportValue_insert hnot
            linarith [hu.value_le, hvalue]
          · intro _
            exact htopMem
        · constructor
          · exact fun h => (htopMem h).elim
          · intro hselected
            have htake :=
              (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) d).1 hselected
            have herase : u.erase (d + 1) = u :=
              Finset.erase_eq_of_notMem htopMem
            rw [herase] at hprefix
            have hgap := mersenneTail_lt_weight (Nat.succ_pos d)
            linarith [hu.le_value_add_tail]
      · have hnd : n ≤ d := by omega
        have hagree := hagreeParent n hn hnd
        simpa [Finset.mem_erase, htopIndex] using hagree

/-- **Packet (24), word form.**  A fatal gap certified over a finite word
excludes the half target for every support agreeing with that word below
the gap rank. -/
theorem half_ne_of_prefix_gap {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2)
    (hhi : (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1))
    {A : Set ℕ} (hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u)) :
    positiveMersenneSupportValue A ≠ (1 / 2 : ℝ) := by
  have hpre := mersenneSupportPrefix_eq_coe_finset hu hagree
  exact positiveMersenneSupportValue_ne_of_rank_gap
    (by rw [hpre]; exact hlo) (by rw [hpre]; exact hhi)

/-- A finite half-gap witness in the cut-locator coordinates. -/
def ExistsFatalHalfGap : Prop :=
  ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2 ∧
    (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1)

/-- A fatal half-gap witness is global, not merely branch-local.  Its two
strict inequalities already make its finite word a depth-`d` straddle; the
canonicality theorem therefore identifies that word with the actual greedy
prefix, after which the word-level exclusion applies to every hypothetical
half representation. -/
theorem half_not_mem_mersenneAchievementSet_of_exists_fatal_gap
    (hgap : ExistsFatalHalfGap) :
    (1 / 2 : ℝ) ∉ mersenneAchievementSet := by
  rcases hgap with ⟨u, d, hu, hlo, hhi⟩
  have htailNonneg := mersenneTail_nonneg (d + 1)
  have htail := mersenneTail_eq_weight_add d
  have hstraddle : IsStraddlePrefix (1 / 2 : ℝ) u d := by
    refine ⟨hu, ?_, ?_⟩
    · linarith
    · linarith
  have hcanonical := hstraddle.half_agrees_greedy
  rintro ⟨A, hA0, hvalue⟩
  have hsupport : greedyMersenneSupport (1 / 2 : ℝ) = A := by
    rw [hvalue, greedySupport_supportValue_eq A hA0]
  have hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u) := by
    intro n hn hnd
    rw [← hsupport]
    exact (hcanonical n hn hnd).symm
  exact (half_ne_of_prefix_gap hu hlo hhi hagree) hvalue.symm

/-! ## Global mechanism dichotomy -/

/-- The empty word straddles the half target at depth zero. -/
theorem initial_half_straddle_zero :
    IsStraddlePrefix (1 / 2 : ℝ) ∅ 0 := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [positiveMersenneSupportValue_coe_finset]
    simp only [Finset.sum_empty]
    norm_num
  · rw [positiveMersenneSupportValue_coe_finset]
    simp only [Finset.sum_empty, zero_add]
    have h := mersenneTail_eq_weight_add 0
    have hw : mersenneWeight 1 = 1 := by norm_num [mersenneWeight]
    have hnn := mersenneTail_nonneg 1
    linarith

/-- **Packet §8/§9 base case.**  The empty word still straddles at depth
one: the depth-one tail exceeds `19/35 > 1/2`. -/
theorem initial_half_straddle :
    IsStraddlePrefix (1 / 2 : ℝ) ∅ 1 := by
  refine ⟨by simp, ?_, ?_⟩
  · rw [positiveMersenneSupportValue_coe_finset]
    simp only [Finset.sum_empty]
    norm_num
  · rw [positiveMersenneSupportValue_coe_finset]
    simp only [Finset.sum_empty, zero_add]
    have hsum : ∑ k ∈ Finset.range 3, mersenneWeight (1 + k + 1)
        = 19 / 35 := by
      simp [Finset.sum_range_succ, mersenneWeight]
      norm_num
    have hpartial : (19 / 35 : ℝ) ≤ mersenneTail 1 := by
      calc
        (19 / 35 : ℝ) = ∑ k ∈ Finset.range 3, mersenneWeight (1 + k + 1) :=
          hsum.symm
        _ ≤ mersenneTail 1 :=
          (summable_mersenneTail 1).sum_le_tsum (Finset.range 3)
            (fun k _ => (mersenneWeight_pos (by omega)).le)
    linarith

/-- **No fatal gap forces membership.**  If no finite word ever certifies a
fatal Mersenne gap, the rank-step trichotomy produces straddle words at
every depth and the closed-set criterion achieves `1/2`. -/
theorem half_mem_mersenneAchievementSet_of_no_fatal_gap
    (hnogap : ∀ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) →
      ¬ (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
            < 1 / 2 ∧
          (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
            + mersenneWeight (d + 1))) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply mem_mersenneAchievementSet_of_straddle_all_depths
  intro d
  induction d with
  | zero => exact ⟨∅, initial_half_straddle_zero⟩
  | succ d ih =>
      obtain ⟨u, hu⟩ := ih
      rcases isStraddlePrefix_step_trichotomy hu with h | h | h
      · exact ⟨u, h⟩
      · exact ⟨insert (d + 1) u, h⟩
      · exact absurd h (hnogap u d hu.mem_bounds)

/-- **Packet (29): the complete mechanism dichotomy.**  Either some finite
word certifies a fatal Mersenne gap — a finite, exact, checkable
nonmembership certificate against all its extensions — or `1/2` is achieved.
Deciding that the fatal branch never fires is exactly the open half case of
Erdős #257; no branch decision is claimed here. -/
theorem half_mem_mersenneAchievementSet_or_exists_fatal_gap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
          < 1 / 2 ∧
        (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
          + mersenneWeight (d + 1) := by
  by_cases hgap : ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
      positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
        < 1 / 2 ∧
      (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
        + mersenneWeight (d + 1)
  · exact Or.inr hgap
  · refine Or.inl (half_mem_mersenneAchievementSet_of_no_fatal_gap ?_)
    intro u d hu hcontra
    exact hgap ⟨u, d, hu, hcontra.1, hcontra.2⟩

/-- The cut-locator fatal branch is exactly the complement of half
membership.  The reverse direction uses the landed global dichotomy; the
forward direction is the new canonical-prefix exclusion above. -/
theorem existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet :
    ExistsFatalHalfGap ↔ (1 / 2 : ℝ) ∉ mersenneAchievementSet := by
  constructor
  · exact half_not_mem_mersenneAchievementSet_of_exists_fatal_gap
  · intro hnot
    rcases half_mem_mersenneAchievementSet_or_exists_fatal_gap with
      hmem | hgap
    · exact (hnot hmem).elim
    · exact hgap

/-- Positive form of the complete cut-locator classification. -/
theorem half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ¬ ExistsFatalHalfGap := by
  rw [existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet]
  tauto

/-! ## Exact regression fixtures -/

/-- **Packet §9 first crossed boundary.**  Selecting `{2,3,6,7}` from the
half target leaves the exact rational residual `1/16002`: the `m = 3`
boundary at `51/128` resolves to a right refinement. -/
theorem half_sub_four_term_prefix_eq :
    (1 / 2 : ℚ) - finiteErdosSum ({2, 3, 6, 7} : Finset ℕ) 2 = 1 / 16002 := by
  norm_num [finiteErdosSum]

/-- **Packet §9 first window.**  The depth-one correction tail is at most
`5/42`. -/
theorem mersenneCorrectionTail_one_le :
    mersenneCorrectionTail 1 ≤ 5 / 42 := by
  have h := mersenneCorrectionTail_le 1
  norm_num at h
  linarith

/-- **Packet §9 boundary-free first macrostep.**  The depth-one correction
window sits strictly above `3/8`, so the first refinement crosses no dyadic
boundary. -/
theorem three_eighths_lt_half_sub_mersenneCorrectionTail_one :
    (3 / 8 : ℝ) < 1 / 2 - mersenneCorrectionTail 1 := by
  have h := mersenneCorrectionTail_one_le
  linarith

end Erdos249257
