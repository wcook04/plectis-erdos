import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import ErdosProblems.Erdos269.ResidueEscape
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Log

/-!
# Erdős #269: restricted floor sums and local windows

Problem-owned landing surface for the exact true-shell floor sums and the
local-window residue reduction.  No declaration here asserts the open
cofinal anti-concentration theorem.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-! ## Exact finite strict counts -/

/-- Strict `{p,q,r}`-smooth exponent prefix.  The ambient exponent box of
side `x` is deliberately redundant; it gives a finite, integer-only carrier
for the strict inequality used by the returned floor-sum formula. -/
def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x

/-- Exact strict smooth-number count in the finite exponent model. -/
def smoothCountLT (p q r x : ℕ) : ℕ :=
  (strictSmoothExponents p q r x).card

/-- Swapping the first two prime channels does not change the strict smooth
count.  This lets pure-power formulas use the jumping prime as their logarithm
base on either endpoint of a shell. -/
theorem smoothCountLT_swap_first_second (p q r x : ℕ) :
    smoothCountLT p q r x = smoothCountLT q p r x := by
  classical
  unfold smoothCountLT
  apply Finset.card_bij (fun z _hz => (z.2.1, z.1, z.2.2))
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzBox, hzVal⟩
    rcases Finset.mem_product.mp hzBox with ⟨hi, hjk⟩
    rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨hj, Finset.mem_product.mpr ⟨hi, hk⟩⟩, ?_⟩
    simpa [smooth3Val, mul_assoc, mul_left_comm, mul_comm] using hzVal
  · intro z₁ _hz₁ z₂ _hz₂ hEq
    rcases z₁ with ⟨i₁, j₁, k₁⟩
    rcases z₂ with ⟨i₂, j₂, k₂⟩
    injection hEq with hj hrest
    injection hrest with hi hk
    simp only at hi hj hk
    exact Prod.ext hi (Prod.ext hj hk)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzBox, hzVal⟩
    rcases Finset.mem_product.mp hzBox with ⟨hj, hik⟩
    rcases Finset.mem_product.mp hik with ⟨hi, hk⟩
    refine ⟨(z.2.1, z.1, z.2.2), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨hi, Finset.mem_product.mpr ⟨hj, hk⟩⟩, ?_⟩
      simpa [smooth3Val, mul_assoc, mul_left_comm, mul_comm] using hzVal
    · rcases z with ⟨j, i, k⟩
      rfl

/-- The strict exponent prefixes are monotone in their cutoff. -/
theorem strictSmoothExponents_mono
    (p q r : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    strictSmoothExponents p q r x ⊆ strictSmoothExponents p q r y := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨hbox, hval⟩
  rcases Finset.mem_product.mp hbox with ⟨hi, hjk⟩
  rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hxy), ?_⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hxy),
      Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hxy)⟩
  · exact hval.trans_le hxy

/-- Exact shell between two strict cutoffs. -/
def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x

/-- Shell cardinality is exactly the difference of the two strict counting
functions.  This is the finite set-theoretic core of `m_N = Ψ(u_{N+1}) -
Ψ(u_N)`. -/
theorem strictSmoothShell_card
    (p q r : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    (strictSmoothShell p q r x y).card =
      smoothCountLT p q r y - smoothCountLT p q r x := by
  exact Finset.card_sdiff_of_subset (strictSmoothExponents_mono p q r hxy)

/-- Restricted count at a pure `p`-power cutoff.  This is the integer carrier
whose two-dimensional floor-sum evaluation is the next formalization seam. -/
def restrictedPurePowerCount (p q r a : ℕ) : ℕ :=
  smoothCountLT p q r (p ^ a)

theorem smoothCountLT_pow_eq_restrictedPurePowerCount
    (p q r a : ℕ) :
    smoothCountLT p q r (p ^ a) = restrictedPurePowerCount p q r a :=
  rfl

/-! ## Exact two-dimensional fiber formula -/

/-- The admissible `(q,r)` exponent pairs below a strict cutoff.  Once such
a pair is fixed, only the remaining `p`-exponent has to be counted. -/
def strictSmoothPairs (q r x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range x).product (Finset.range x)).filter
    fun e => q ^ e.1 * r ^ e.2 < x

/-- The admissible two-dimensional exponent pairs are monotone in the
cutoff. -/
theorem strictSmoothPairs_mono
    (q r : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    strictSmoothPairs q r x ⊆ strictSmoothPairs q r y := by
  intro e he
  rcases Finset.mem_filter.mp he with ⟨heBox, heVal⟩
  rcases Finset.mem_product.mp heBox with ⟨hj, hk⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, heVal.trans_le hxy⟩
  · exact Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hxy)
  · exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le hxy)

/-- The restricted two-dimensional fiber sum: for every admissible `(q,r)`
pair, count exactly the `p`-exponents that keep the smooth value below `x`.
This is an integer-only version of the returned restricted floor sum. -/
def restrictedFiberCount (p q r x : ℕ) : ℕ :=
  ∑ e ∈ strictSmoothPairs q r x,
    ((strictSmoothExponents p q r x).filter
      fun z => (z.2.1, z.2.2) = e).card

/-- The explicit one-dimensional `p`-exponent fiber over a fixed `(q,r)`
pair. -/
def strictPExponentFiber (p q r x : ℕ) (e : ℕ × ℕ) : Finset ℕ :=
  (Finset.range x).filter fun i =>
    p ^ i * (q ^ e.1 * r ^ e.2) < x

/-- A one-dimensional exponent fiber at a pure power cutoff has the exact
length predicted by the natural logarithm. -/
theorem strictPExponentFiber_card_at_pow
    (p q r a : ℕ) {e : ℕ × ℕ}
    (hp : 1 < p) (hq : 0 < q) (hr : 0 < r)
    (he : e ∈ strictSmoothPairs q r (p ^ a)) :
    (strictPExponentFiber p q r (p ^ a) e).card =
      a - Nat.log p (q ^ e.1 * r ^ e.2) := by
  classical
  let t := q ^ e.1 * r ^ e.2
  have ht : 0 < t := by
    dsimp [t]
    exact Nat.mul_pos (Nat.pow_pos hq) (Nat.pow_pos hr)
  have htCut : t < p ^ a := (Finset.mem_filter.mp he).2
  have hset : strictPExponentFiber p q r (p ^ a) e =
      Finset.range (a - Nat.log p t) := by
    ext i
    simp only [strictPExponentFiber, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_hiRange, hiVal⟩
      have hpowLog : p ^ Nat.log p t ≤ t := Nat.pow_log_le_self p ht.ne'
      have hpowBound : p ^ (i + Nat.log p t) < p ^ a := by
        rw [pow_add]
        exact (Nat.mul_le_mul_left (p ^ i) hpowLog).trans_lt hiVal
      have hiLog : i + Nat.log p t < a :=
        (Nat.pow_lt_pow_iff_right hp).mp hpowBound
      omega
    · intro hi
      have hiA : i < a := by omega
      refine ⟨hiA.trans (Nat.lt_pow_self hp), ?_⟩
      have htUpper : t < p ^ (Nat.log p t + 1) :=
        Nat.lt_pow_succ_log_self hp t
      calc
        p ^ i * (q ^ e.1 * r ^ e.2) = p ^ i * t := by rfl
        _ < p ^ i * p ^ (Nat.log p t + 1) :=
          (Nat.mul_lt_mul_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))).mpr htUpper
        _ = p ^ (i + (Nat.log p t + 1)) :=
          (pow_add p i (Nat.log p t + 1)).symm
        _ ≤ p ^ a := Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp) (by omega)
  rw [hset, Finset.card_range]

/-- The literal restricted two-dimensional floor sum: sum the sizes of the
explicit `p`-exponent fibers over all admissible `(q,r)` pairs. -/
def restrictedFloorSum (p q r x : ℕ) : ℕ :=
  ∑ e ∈ strictSmoothPairs q r x,
    (strictPExponentFiber p q r x e).card

/-- Closed natural-log form of the restricted floor sum at the pure cutoff
`p^a`.  Every summand is the exact number of admissible `p`-exponents above
the fixed `(q,r)` pair. -/
def restrictedLogFloorSum (p q r a : ℕ) : ℕ :=
  ∑ e ∈ strictSmoothPairs q r (p ^ a),
    (a - Nat.log p (q ^ e.1 * r ^ e.2))

/-- The explicit fiber sum at `p^a` is exactly its closed logarithmic form. -/
theorem restrictedFloorSum_pow_eq_restrictedLogFloorSum
    (p q r a : ℕ) (hp : 1 < p) (hq : 0 < q) (hr : 0 < r) :
    restrictedFloorSum p q r (p ^ a) = restrictedLogFloorSum p q r a := by
  classical
  unfold restrictedFloorSum restrictedLogFloorSum
  apply Finset.sum_congr rfl
  intro e he
  exact strictPExponentFiber_card_at_pow p q r a hp hq hr he

/-- Exact discrete derivative of the restricted floor sums.  This is the
returned identity `V_p(a+1) - V_p(a) = W_p(a+1)`, with `W_p(a+1)` represented
by the cardinality of the admissible `(q,r)` exponent pairs below
`p^(a+1)`. -/
theorem restrictedLogFloorSum_succ_sub
    (p q r a : ℕ) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    restrictedLogFloorSum p q r (a + 1) -
        restrictedLogFloorSum p q r a =
      (strictSmoothPairs q r (p ^ (a + 1))).card := by
  classical
  let s := strictSmoothPairs q r (p ^ a)
  let t := strictSmoothPairs q r (p ^ (a + 1))
  have hpow : p ^ a ≤ p ^ (a + 1) :=
    Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp) (Nat.le_succ a)
  have hst : s ⊆ t := strictSmoothPairs_mono q r hpow
  have hold : ∀ e ∈ s,
      (a + 1 - Nat.log p (q ^ e.1 * r ^ e.2)) =
        (a - Nat.log p (q ^ e.1 * r ^ e.2)) + 1 := by
    intro e he
    have ht : 0 < q ^ e.1 * r ^ e.2 :=
      Nat.mul_pos (Nat.pow_pos (Nat.zero_lt_of_lt hq))
        (Nat.pow_pos (Nat.zero_lt_of_lt hr))
    have hlt : q ^ e.1 * r ^ e.2 < p ^ a :=
      (Finset.mem_filter.mp he).2
    have hlog : Nat.log p (q ^ e.1 * r ^ e.2) < a :=
      Nat.log_lt_of_lt_pow ht.ne' hlt
    omega
  have hnew : ∀ e ∈ t \ s,
      (a + 1 - Nat.log p (q ^ e.1 * r ^ e.2)) = 1 := by
    intro e he
    have heT := (Finset.mem_sdiff.mp he).1
    have heNotS := (Finset.mem_sdiff.mp he).2
    have hlt : q ^ e.1 * r ^ e.2 < p ^ (a + 1) :=
      (Finset.mem_filter.mp heT).2
    have hle : p ^ a ≤ q ^ e.1 * r ^ e.2 := by
      by_contra h
      apply heNotS
      rcases Finset.mem_filter.mp heT with ⟨heBox, _⟩
      rcases Finset.mem_product.mp heBox with ⟨_hj, _hk⟩
      have hpair : q ^ e.1 * r ^ e.2 < p ^ a := by omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, by omega⟩
      · apply Finset.mem_range.mpr
        exact ((Nat.lt_pow_self hq).trans_le
          (Nat.le_mul_of_pos_right _
            (Nat.pow_pos (Nat.zero_lt_of_lt hr)))).trans hpair
      · apply Finset.mem_range.mpr
        exact ((Nat.lt_pow_self hr).trans_le
          (Nat.le_mul_of_pos_left _
            (Nat.pow_pos (Nat.zero_lt_of_lt hq)))).trans hpair
    have hlog : Nat.log p (q ^ e.1 * r ^ e.2) = a :=
      Nat.log_eq_of_pow_le_of_lt_pow hle hlt
    omega
  have hsucc : restrictedLogFloorSum p q r (a + 1) =
      restrictedLogFloorSum p q r a + t.card := by
    unfold restrictedLogFloorSum
    change (∑ e ∈ t, (a + 1 - Nat.log p (q ^ e.1 * r ^ e.2))) =
      (∑ e ∈ s, (a - Nat.log p (q ^ e.1 * r ^ e.2))) + t.card
    rw [← Finset.sum_sdiff hst]
    rw [Finset.sum_congr rfl hold, Finset.sum_congr rfl hnew]
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      mul_one, Finset.card_sdiff_of_subset hst]
    have hcard : s.card ≤ t.card := Finset.card_le_card hst
    calc
      (t.card - s.card) +
          ((∑ e ∈ s, (a - Nat.log p (q ^ e.1 * r ^ e.2))) + s.card) =
        (∑ e ∈ s, (a - Nat.log p (q ^ e.1 * r ^ e.2))) +
          ((t.card - s.card) + s.card) := by ac_rfl
      _ = (∑ e ∈ s, (a - Nat.log p (q ^ e.1 * r ^ e.2))) + t.card := by
        rw [Nat.sub_add_cancel hcard]
  rw [hsucc]
  exact Nat.add_sub_cancel_left _ _

/-- The abstract projection fiber is exactly the explicit `p`-exponent
fiber. -/
theorem strictSmoothExponent_fiber_card
    (p q r x : ℕ) {e : ℕ × ℕ} (he : e ∈ strictSmoothPairs q r x) :
    ((strictSmoothExponents p q r x).filter
      fun z => (z.2.1, z.2.2) = e).card =
      (strictPExponentFiber p q r x e).card := by
  classical
  apply Finset.card_bij (fun z _hz => z.1)
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzSmooth, hzProj⟩
    rcases Finset.mem_filter.mp hzSmooth with ⟨hzBox, hzVal⟩
    rcases Finset.mem_product.mp hzBox with ⟨hi, _hjk⟩
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    have hj : z.2.1 = e.1 := congrArg Prod.fst hzProj
    have hk : z.2.2 = e.2 := congrArg Prod.snd hzProj
    rw [← hj, ← hk]
    simpa [smooth3Val, mul_assoc] using hzVal
  · intro z₁ hz₁ z₂ hz₂ hfirst
    have hproj₁ := (Finset.mem_filter.mp hz₁).2
    have hproj₂ := (Finset.mem_filter.mp hz₂).2
    apply Prod.ext hfirst
    apply Prod.ext
    · exact (congrArg Prod.fst hproj₁).trans (congrArg Prod.fst hproj₂).symm
    · exact (congrArg Prod.snd hproj₁).trans (congrArg Prod.snd hproj₂).symm
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hiRange, hiVal⟩
    rcases Finset.mem_filter.mp he with ⟨heBox, _heVal⟩
    rcases Finset.mem_product.mp heBox with ⟨hj, hk⟩
    refine ⟨(i, e.1, e.2), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hiRange, Finset.mem_product.mpr ⟨hj, hk⟩⟩, ?_⟩, rfl⟩
    simpa [smooth3Val, mul_assoc] using hiVal

/-- Replacing every projection fiber by its explicit exponent count turns the
abstract fiber decomposition into the returned restricted floor sum. -/
theorem restrictedFiberCount_eq_restrictedFloorSum
    (p q r x : ℕ) :
    restrictedFiberCount p q r x = restrictedFloorSum p q r x := by
  classical
  unfold restrictedFiberCount restrictedFloorSum
  apply Finset.sum_congr rfl
  intro e he
  exact strictSmoothExponent_fiber_card p q r x he

/-- Exact dimension reduction of the three-prime smooth count to a restricted
two-dimensional sum of one-dimensional fibers. -/
theorem smoothCountLT_eq_restrictedFiberCount
    (p q r x : ℕ) (hp : 0 < p) :
    smoothCountLT p q r x = restrictedFiberCount p q r x := by
  classical
  unfold smoothCountLT restrictedFiberCount
  apply Finset.card_eq_sum_card_fiberwise
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hbox, hval⟩
  rcases Finset.mem_product.mp hbox with ⟨_hi, hjk⟩
  rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hj, hk⟩, ?_⟩
  have hval' : p ^ z.1 * (q ^ z.2.1 * r ^ z.2.2) < x := by
    simpa [smooth3Val, mul_assoc] using hval
  exact
    (Nat.le_mul_of_pos_left (q ^ z.2.1 * r ^ z.2.2)
      (Nat.pow_pos hp : 0 < p ^ z.1)).trans_lt hval'

/-- Exact restricted two-dimensional floor-sum formula for the strict
three-prime smooth count. -/
theorem smoothCountLT_eq_restrictedFloorSum
    (p q r x : ℕ) (hp : 0 < p) :
    smoothCountLT p q r x = restrictedFloorSum p q r x := by
  rw [smoothCountLT_eq_restrictedFiberCount p q r x hp,
    restrictedFiberCount_eq_restrictedFloorSum]

/-- At a pure `p`-power cutoff, the exact restricted count is therefore the
returned two-dimensional fiber sum. -/
theorem restrictedPurePowerCount_eq_fiberSum
    (p q r a : ℕ) (hp : 0 < p) :
    restrictedPurePowerCount p q r a = restrictedFiberCount p q r (p ^ a) := by
  exact smoothCountLT_eq_restrictedFiberCount p q r (p ^ a) hp

/-- At a pure `p`-power cutoff, the exact count is the literal restricted
two-dimensional floor sum. -/
theorem restrictedPurePowerCount_eq_restrictedFloorSum
    (p q r a : ℕ) (hp : 0 < p) :
    restrictedPurePowerCount p q r a = restrictedFloorSum p q r (p ^ a) := by
  exact smoothCountLT_eq_restrictedFloorSum p q r (p ^ a) hp

/-- Kernel-checked form of the returned identity `Ψ(p^a) = V_p(a)`: the
strict three-prime smooth count at a pure power equals the explicit restricted
two-dimensional natural-log floor sum. -/
theorem restrictedPurePowerCount_eq_restrictedLogFloorSum
    (p q r a : ℕ) (hp : 1 < p) (hq : 0 < q) (hr : 0 < r) :
    restrictedPurePowerCount p q r a = restrictedLogFloorSum p q r a := by
  rw [restrictedPurePowerCount_eq_restrictedFloorSum p q r a
      (Nat.zero_lt_of_lt hp),
    restrictedFloorSum_pow_eq_restrictedLogFloorSum p q r a hp hq hr]

/-- The exact pure-power shell is the difference of two restricted
two-dimensional fiber sums.  This is the kernel-checked form of the returned
identity `m_N = V_q(b) - V_p(a)` before choosing adjacent jump labels. -/
theorem strictSmoothShell_card_eq_restrictedFiberCount_sub
    (p q r : ℕ) (hp : 0 < p) {x y : ℕ} (hxy : x ≤ y) :
    (strictSmoothShell p q r x y).card =
      restrictedFiberCount p q r y - restrictedFiberCount p q r x := by
  rw [strictSmoothShell_card p q r hxy,
    smoothCountLT_eq_restrictedFiberCount p q r y hp,
    smoothCountLT_eq_restrictedFiberCount p q r x hp]

/-- Exact shell multiplicity as a difference of two literal restricted
two-dimensional floor sums. -/
theorem strictSmoothShell_card_eq_restrictedFloorSum_sub
    (p q r : ℕ) (hp : 0 < p) {x y : ℕ} (hxy : x ≤ y) :
    (strictSmoothShell p q r x y).card =
      restrictedFloorSum p q r y - restrictedFloorSum p q r x := by
  rw [strictSmoothShell_card p q r hxy,
    smoothCountLT_eq_restrictedFloorSum p q r y hp,
    smoothCountLT_eq_restrictedFloorSum p q r x hp]

/-- If a shell runs from a pure `p`-power to a pure `q`-power, its
multiplicity is exactly `V_q(b) - V_p(a)` in the returned notation. -/
theorem strictSmoothShell_card_between_purePowers
    (p q r a b : ℕ) (hp : 1 < p) (hq : 1 < q) (hr : 0 < r)
    (hpq : p ^ a ≤ q ^ b) :
    (strictSmoothShell p q r (p ^ a) (q ^ b)).card =
      restrictedLogFloorSum q p r b - restrictedLogFloorSum p q r a := by
  rw [strictSmoothShell_card p q r hpq,
    smoothCountLT_swap_first_second p q r (q ^ b),
    smoothCountLT_pow_eq_restrictedPurePowerCount,
    restrictedPurePowerCount_eq_restrictedLogFloorSum q p r b hq
      (Nat.zero_lt_of_lt hp) hr,
    smoothCountLT_pow_eq_restrictedPurePowerCount,
    restrictedPurePowerCount_eq_restrictedLogFloorSum p q r a hp
      (Nat.zero_lt_of_lt hq) hr]

/-! ## Generic logarithmic-window algebra -/

/-- Multiplicative base accumulated across a local window. -/
def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 1
  | len + 1 => b (lo + len) * windowBase b lo len

/-- Affine forcing accumulated across the same local window. -/
def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)

/-- Weighted correction emitted when the forcing word is a discrete
derivative `V(n+1)-V(n)`.  Recursively this is the local weighted sum of the
interior potentials with coefficients `(b_n-1)` and all later bases. -/
def windowPotentialCorrection (b V : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 =>
      b (lo + len) * windowPotentialCorrection b V lo len +
        (b (lo + len) - 1) * V (lo + len)

/-- Exact summation-by-parts expansion of a local forcing numerator whose
digits are consecutive differences of a potential.  This is the recursive,
division-free form of the packet's weighted floor-sum formula for
`R_(lo,h)`. -/
theorem windowForcing_difference_eq_potential
    (b V : ℕ → ℤ) (lo len : ℕ) :
    windowForcing b (fun n => V (n + 1) - V n) lo len =
      V (lo + len) - windowBase b lo len * V lo +
        windowPotentialCorrection b V lo len := by
  induction len with
  | zero => simp [windowForcing, windowBase, windowPotentialCorrection]
  | succ len ih =>
      simp only [windowForcing, windowBase, windowPotentialCorrection, ih]
      rw [show lo + len + 1 = lo + (len + 1) by omega]
      ring

/-- Any first-order affine recurrence unrolls exactly into the local base and
local forcing.  This is the algebraic heart of the logarithmic-window
compression and is independent of the still-open floor-sum anti-concentration
producer. -/
theorem affineRecurrence_window
    (A b e : ℕ → ℤ) (lo len : ℕ)
    (hrec : ∀ n, A (n + 1) = b n * A n + e n) :
    A (lo + len) =
      windowBase b lo len * A lo + windowForcing b e lo len := by
  induction len with
  | zero => simp [windowBase, windowForcing]
  | succ len ih =>
      rw [Nat.add_succ, hrec, ih]
      simp only [windowBase, windowForcing]
      ring

/-- Scaling every forcing term scales the accumulated local numerator by the
same constant. -/
theorem windowForcing_const_mul
    (b e : ℕ → ℤ) (B : ℤ) (lo len : ℕ) :
    windowForcing b (fun n => B * e n) lo len =
      B * windowForcing b e lo len := by
  induction len with
  | zero => simp [windowForcing]
  | succ len ih =>
      simp only [windowForcing, ih]
      ring

/-- Integral-carry form of the local-window identity. -/
theorem integralCarry_window
    (c b m : ℕ → ℤ) (B : ℤ) (lo len : ℕ)
    (hrec : ∀ n, c (n + 1) = b n * c n - B * m n) :
    c (lo + len) =
      windowBase b lo len * c lo -
        B * windowForcing b m lo len := by
  have hrec' : ∀ n, c (n + 1) = b n * c n + (-B) * m n := by
    intro n
    rw [hrec]
    ring
  rw [affineRecurrence_window c b (fun n => (-B) * m n) lo len hrec']
  rw [windowForcing_const_mul b m (-B) lo len]
  ring

/-- If the endpoint carry is positive and lies in the canonical window for
the accumulated base, then the window's least positive forcing residue is
exactly that endpoint carry. -/
theorem leastPositiveResidue_windowForcing_eq_carry
    (c b m : ℕ → ℤ) (B : ℤ) (lo len : ℕ)
    (hrec : ∀ n, c (n + 1) = b n * c n - B * m n)
    (hWpos : 0 < windowBase b lo len)
    (hcpos : 0 < c (lo + len))
    (hcle :
      Int.natAbs (c (lo + len)) ≤
        Int.natAbs (windowBase b lo len)) :
    leastPositiveResidue
        (Int.natAbs (windowBase b lo len))
        (-B * windowForcing b m lo len) =
      Int.natAbs (c (lo + len)) := by
  let W : ℤ := windowBase b lo len
  let F : ℤ := windowForcing b m lo len
  have hwindow :
      c (lo + len) = W * c lo - B * F := by
    simpa [W, F] using integralCarry_window c b m B lo len hrec
  have hmodW :
      Int.ModEq W (c (lo + len)) (-B * F) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-c lo, ?_⟩
    rw [hwindow]
    ring
  have hmod :
      Int.ModEq (Int.natAbs W) (c (lo + len)) (-B * F) :=
    (Int.modEq_natAbs).2 hmodW
  exact leastPositiveResidue_eq_natAbs_of_pos_le_modEq
    (Int.natAbs_pos.mpr hWpos.ne')
    hcpos
    (by simpa [W] using hcle)
    (by simpa [W, F] using hmod)

/-- When shell multiplicities are exact differences of smooth-count
potentials, the integral-carry window is an explicit weighted potential
identity. -/
theorem integralCarry_window_potential
    (c b V : ℕ → ℤ) (B : ℤ) (lo len : ℕ)
    (hrec : ∀ n,
      c (n + 1) = b n * c n - B * (V (n + 1) - V n)) :
    c (lo + len) =
      windowBase b lo len * c lo -
        B * (V (lo + len) - windowBase b lo len * V lo +
          windowPotentialCorrection b V lo len) := by
  rw [integralCarry_window c b (fun n => V (n + 1) - V n) B lo len hrec,
    windowForcing_difference_eq_potential]

/-! ## Exact denominator-factor cancellation -/

/-- Any fixed `{p,q,r}`-smooth factor divides the running three-prime height
as soon as the cutoff reaches that factor.  This is the exact absorption step
used before cancelling the smooth part of a hypothetical denominator. -/
theorem smooth3Val_dvd_threePrimeHeight_of_le
    {p q r i j k x : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hcut : smooth3Val p q r i j k ≤ x) :
    smooth3Val p q r i j k ∣ threePrimeHeight p q r x := by
  have hpPow : p ^ i ≤ smooth3Val p q r i j k := by
    unfold smooth3Val
    exact (Nat.le_mul_of_pos_right _
      (Nat.pow_pos (Nat.zero_lt_of_lt hq))).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.zero_lt_of_lt hr)))
  have hqPow : q ^ j ≤ smooth3Val p q r i j k := by
    unfold smooth3Val
    exact (Nat.le_mul_of_pos_left _
      (Nat.pow_pos (Nat.zero_lt_of_lt hp))).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.zero_lt_of_lt hr)))
  have hrPow : r ^ k ≤ smooth3Val p q r i j k := by
    unfold smooth3Val
    exact Nat.le_mul_of_pos_left _
      (Nat.mul_pos (Nat.pow_pos (Nat.zero_lt_of_lt hp))
        (Nat.pow_pos (Nat.zero_lt_of_lt hq)))
  have hi : i ≤ Nat.log p x :=
    Nat.le_log_of_pow_le hp (hpPow.trans hcut)
  have hj : j ≤ Nat.log q x :=
    Nat.le_log_of_pow_le hq (hqPow.trans hcut)
  have hk : k ≤ Nat.log r x :=
    Nat.le_log_of_pow_le hr (hrPow.trans hcut)
  exact mul_dvd_mul (mul_dvd_mul (pow_dvd_pow p hi) (pow_dvd_pow q hj))
    (pow_dvd_pow r hk)

/-- Cancel a common nonzero factor from every state of an integral carry
recurrence.  In the packet application, `smoothFactor` is the absorbed
`{2,3,5}`-smooth part of a hypothetical denominator and `reducedDenominator`
is therefore coprime to `30`. -/
theorem integralCarry_cancel_commonFactor
    (c d b m : ℕ → ℤ) (smoothFactor reducedDenominator : ℤ)
    (hsmooth : smoothFactor ≠ 0)
    (hfactor : ∀ n, c n = smoothFactor * d n)
    (hrec : ∀ n,
      c (n + 1) = b n * c n -
        (smoothFactor * reducedDenominator) * m n) :
    ∀ n, d (n + 1) = b n * d n - reducedDenominator * m n := by
  intro n
  apply mul_left_cancel₀ hsmooth
  calc
    smoothFactor * d (n + 1) = c (n + 1) := (hfactor (n + 1)).symm
    _ = b n * c n - (smoothFactor * reducedDenominator) * m n := hrec n
    _ = smoothFactor * (b n * d n - reducedDenominator * m n) := by
      rw [hfactor n]
      ring

/-- Positivity and an upper bound descend through the same positive common
factor.  This is the exact bound transfer `0 < c_n ≤ B_sm B_0 K_n` to
`0 < d_n ≤ B_0 K_n`. -/
theorem reducedCarry_pos_le_of_commonFactor
    {c d smoothFactor reducedDenominator K : ℤ}
    (hsmooth : 0 < smoothFactor)
    (hfactor : c = smoothFactor * d)
    (hcpos : 0 < c)
    (hcbound : c ≤ smoothFactor * (reducedDenominator * K)) :
    0 < d ∧ d ≤ reducedDenominator * K := by
  constructor <;> nlinarith

/-- The reduced carry therefore inherits the exact logarithmic-window
identity with the reduced denominator as multiplier. -/
theorem reducedIntegralCarry_window
    (c d b m : ℕ → ℤ) (smoothFactor reducedDenominator : ℤ)
    (hsmooth : smoothFactor ≠ 0)
    (hfactor : ∀ n, c n = smoothFactor * d n)
    (hrec : ∀ n,
      c (n + 1) = b n * c n -
        (smoothFactor * reducedDenominator) * m n)
    (lo len : ℕ) :
    d (lo + len) =
      windowBase b lo len * d lo -
        reducedDenominator * windowForcing b m lo len := by
  exact integralCarry_window d b m reducedDenominator lo len
    (integralCarry_cancel_commonFactor c d b m smoothFactor
      reducedDenominator hsmooth hfactor hrec)

/-- The exact remaining producer after local-window compression.  It is kept
as a named proposition, not asserted as a theorem. -/
def CofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 →
    ∀ lo₀ : ℕ, ∃ lo len : ℕ,
      lo₀ ≤ lo ∧ 0 < len ∧
      0 < Int.natAbs (windowBase (fun n => b n) lo len) ∧
      shortBound B (lo + len) <
        leastPositiveResidue
          (Int.natAbs (windowBase (fun n => b n) lo len))
          (-((B : ℤ) *
            windowForcing (fun n => b n) (fun n => m n) lo len))

/-- The denominator-dependent local-window producer is exactly strong enough
to rule out a positive reduced carry with the matching short bound.  The
coprimality hypothesis belongs to the still-open producer; the checked
consumer uses only the emitted escaping window. -/
theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False := by
  rcases hescape B hBpos hBcoprime 0 with
    ⟨lo, len, _hlo, _hlen, hbasePos, hresidueEscape⟩
  let W : ℤ := windowBase (fun n => (b n : ℤ)) lo len
  let F : ℤ := windowForcing
    (fun n => (b n : ℤ)) (fun n => (m n : ℤ)) lo len
  have hwindow :
      d (lo + len) = W * d lo - (B : ℤ) * F := by
    simpa [W, F] using
      integralCarry_window d
        (fun n => (b n : ℤ)) (fun n => (m n : ℤ))
        (B : ℤ) lo len hrec
  have hmodW :
      Int.ModEq W (d (lo + len)) (-((B : ℤ) * F)) := by
    rw [Int.modEq_iff_dvd]
    refine ⟨-d lo, ?_⟩
    rw [hwindow]
    ring
  have hmod :
      Int.ModEq (Int.natAbs W)
        (d (lo + len)) (-((B : ℤ) * F)) :=
    (Int.modEq_natAbs).2 hmodW
  exact no_bounded_positive_int_state_of_leastPositiveResidue
    (by simpa [W] using hbasePos)
    (hpos (lo + len))
    (hbound (lo + len))
    (by simpa [W, F] using hresidueEscape)
    hmod

/-- A hypothetical carry recurrence with an absorbed nonzero common factor is
already contradictory once its reduced denominator satisfies the same cofinal
local-window escape premise.  This is only a conditional bridge from absorbed
integral carries to the existing reduced-carry consumer; it proves no
irrationality statement without the separate actual-series carry bridge and a
producer for `CofinalLocalWindowEscape`. -/
theorem no_positive_absorbedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (c d : ℕ → ℤ) (smoothFactor : ℤ)
    (hsmooth : smoothFactor ≠ 0)
    (hfactor : ∀ n, c n = smoothFactor * d n)
    (hrec : ∀ n,
      c (n + 1) =
        (b n : ℤ) * c n - (smoothFactor * (B : ℤ)) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False := by
  exact no_positive_reducedCarry_of_cofinalLocalWindowEscape
    b m shortBound hescape B hBpos hBcoprime d
    (integralCarry_cancel_commonFactor c d
      (fun n => (b n : ℤ)) (fun n => (m n : ℤ))
      smoothFactor (B : ℤ) hsmooth hfactor hrec)
    hpos hbound

end ErdosProblems.Erdos269
