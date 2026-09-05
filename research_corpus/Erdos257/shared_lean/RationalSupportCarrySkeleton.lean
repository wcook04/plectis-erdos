import Erdos257PeriodNoncollapse.BooleanMobiusCarry
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Rational support, doubling residues, and reciprocal mass

Suppose the base-two support series has a rational value whose denominator is
written as `2^c * v`, with `v` odd.  Clearing that denominator produces a
positive integer tail state.  Modulo `v`, the state follows a doubling orbit,
and the wrap digits record exactly when doubling crosses the modulus.  The
finite arithmetic begins with the identity

`sum residues = odd modulus * number of wraps`.

When the reciprocal support terms are summable, the Cesàro mean of the support
tails is their sum `reciprocalMass A`.  Combining this mean identity with the
periodic residue arithmetic gives quantitative lower bounds from wrap
frequency and from Boolean collisions.  Common multiples also force every
positive tail state attached to an infinite support to be unbounded.

These are conditional obstructions, not a solution of Erdős #257.  They do
not exclude every rational denominator, and the nonsummable alternative below
is not stated as convergence of partial sums to `+∞`.  Exponent zero remains
excluded from the literal support semantics.  The finite computations at the
end only check examples; the general theorems are proved independently.
-/

namespace Erdos257PeriodNoncollapse

open ArithmeticFunction Filter Set

/-! ## Doubling residues and wrap digits -/

/-- Least nonnegative residue of `p * 2^n` modulo `v`.  When `v` is odd and
`p` is coprime to `v`, this residue is strictly positive. -/
def doublingResidue (p v n : ℕ) : ℕ := (p * 2 ^ n) % v

/-- The quotient expelled when a least residue is doubled.  Since the
residue is below `v`, this quotient is always zero or one. -/
def doublingWrapDigit (p v n : ℕ) : ℕ :=
  (2 * doublingResidue p v n) / v

/-- Number of binary wraps in the first `h` transitions. -/
def doublingWrapCount (p v h : ℕ) : ℕ :=
  ∑ n ∈ Finset.range h, doublingWrapDigit p v n

/-- A period condition, without a minimality requirement: `h > 0` and
`2^h ≡ 1 (mod v)`.  The multiplicative order is one admissible choice. -/
def IsDoublingPeriod (v h : ℕ) : Prop :=
  0 < h ∧ Nat.ModEq v (2 ^ h) 1

theorem doublingResidue_lt (p : ℕ) {v : ℕ} (hv : 0 < v) (n : ℕ) :
    doublingResidue p v n < v := by
  exact Nat.mod_lt _ hv

theorem doublingWrapDigit_le_one (p : ℕ) {v : ℕ} (hv : 0 < v) (n : ℕ) :
    doublingWrapDigit p v n ≤ 1 := by
  unfold doublingWrapDigit
  have hr := doublingResidue_lt p hv n
  apply (Nat.div_le_iff_le_mul hv).2
  omega

theorem doublingWrapDigit_eq_zero_or_one (p : ℕ) {v : ℕ} (hv : 0 < v)
    (n : ℕ) :
    doublingWrapDigit p v n = 0 ∨ doublingWrapDigit p v n = 1 := by
  have h := doublingWrapDigit_le_one p hv n
  omega

/-- For an odd modulus and reduced numerator, every canonical residue is
strictly positive. -/
theorem doublingResidue_pos
    (p : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.Coprime v) (j : ℕ) :
    0 < doublingResidue p v j := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hvdvd : v ∣ p * 2 ^ j := Nat.dvd_of_mod_eq_zero hzero
  have htwo : (2 ^ j).Coprime v :=
    (Nat.coprime_two_left.mpr hvodd).pow_left j
  have hprod : (p * 2 ^ j).Coprime v := hpv.mul_left htwo
  have hvone := Nat.eq_one_of_dvd_coprimes hprod hvdvd (dvd_refl v)
  omega

/-- Doubling and reducing advances the canonical residue cycle by one. -/
theorem doublingResidue_succ (p v n : ℕ) :
    doublingResidue p v (n + 1) = (2 * doublingResidue p v n) % v := by
  have hmod : Nat.ModEq v (p * 2 ^ n) ((p * 2 ^ n) % v) :=
    (Nat.mod_modEq (p * 2 ^ n) v).symm
  have htwo := hmod.mul_left 2
  simp [doublingResidue, pow_succ, mul_comm, mul_left_comm] at htwo ⊢

/-- Exact binary carry recurrence for canonical residues. -/
theorem doublingResidue_carry (p v n : ℕ) :
    2 * doublingResidue p v n =
      v * doublingWrapDigit p v n + doublingResidue p v (n + 1) := by
  rw [doublingResidue_succ]
  unfold doublingWrapDigit
  have h := Nat.div_add_mod (2 * doublingResidue p v n) v
  omega

/-- A doubling period closes every numerator residue cycle. -/
theorem doublingResidue_add_period
    (p : ℕ) {v h : ℕ} (hperiod : IsDoublingPeriod v h) (n : ℕ) :
    doublingResidue p v (n + h) = doublingResidue p v n := by
  have hmod := hperiod.2.mul_left (p * 2 ^ n)
  unfold doublingResidue
  simpa [pow_add, mul_assoc] using hmod

/-- Shifting the tail index multiplies the starting numerator by the same
power of two. -/
theorem doublingResidue_add (p v N j : ℕ) :
    doublingResidue p v (N + j) =
      doublingResidue (p * 2 ^ N) v j := by
  simp [doublingResidue, pow_add, mul_assoc]

/-! ## Generic finite-cycle identities -/

/-- Summing a shifted finite sequence differs only by its two endpoints. -/
theorem sum_range_shift_one (r : ℕ → ℕ) (h : ℕ) :
    (∑ j ∈ Finset.range h, r (j + 1)) + r 0 =
      (∑ j ∈ Finset.range h, r j) + r h := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      omega

/-- Every complete block of a periodic natural sequence has the same sum. -/
theorem sum_range_add_eq_sum_range_of_periodic
    (r : ℕ → ℕ) (h : ℕ) (hperiod : ∀ N : ℕ, r (N + h) = r N) :
    ∀ N : ℕ,
      ∑ j ∈ Finset.range h, r (N + j) =
        ∑ j ∈ Finset.range h, r j := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hshift := sum_range_shift_one (fun j ↦ r (N + j)) h
      have hend : r (N + h) = r N := hperiod N
      rw [hend] at hshift
      have hstep :
          ∑ j ∈ Finset.range h, r (N + (j + 1)) =
            ∑ j ∈ Finset.range h, r (N + j) := by
        simp only [Nat.add_zero] at hshift
        exact Nat.add_right_cancel hshift
      calc
        ∑ j ∈ Finset.range h, r (Nat.succ N + j) =
            ∑ j ∈ Finset.range h, r (N + (j + 1)) := by
              apply Finset.sum_congr rfl
              intro j hj
              congr 1
              omega
        _ = ∑ j ∈ Finset.range h, r (N + j) := hstep
        _ = ∑ j ∈ Finset.range h, r j := ih

/-- **Wrap identity for a closed binary residue cycle.** -/
theorem sum_eq_modulus_mul_wrapCount_of_closed_cycle
    (v h : ℕ) (r k : ℕ → ℕ)
    (hcarry : ∀ j : ℕ, 2 * r j = v * k j + r (j + 1))
    (hclosed : r h = r 0) :
    ∑ j ∈ Finset.range h, r j =
      v * ∑ j ∈ Finset.range h, k j := by
  have hsum : (∑ j ∈ Finset.range h, 2 * r j) =
      ∑ j ∈ Finset.range h, (v * k j + r (j + 1)) :=
    Finset.sum_congr rfl fun j _ ↦ hcarry j
  have hshift := sum_range_shift_one r h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hclosed] at hshift
  omega

/-- Canonical form of the wrap identity. -/
theorem sum_doublingResidue_eq_mul_wrapCount
    (p : ℕ) {v h : ℕ} (hperiod : IsDoublingPeriod v h) :
    ∑ j ∈ Finset.range h, doublingResidue p v j =
      v * doublingWrapCount p v h := by
  apply sum_eq_modulus_mul_wrapCount_of_closed_cycle v h
    (doublingResidue p v) (doublingWrapDigit p v)
  · exact doublingResidue_carry p v
  · simpa using doublingResidue_add_period p hperiod 0

/-- A nonempty positive closed residue cycle has at least one wrap. -/
theorem doublingWrapCount_pos
    (p : ℕ) {v h : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.Coprime v) (hperiod : IsDoublingPeriod v h) :
    0 < doublingWrapCount p v h := by
  have hsum := sum_doublingResidue_eq_mul_wrapCount p hperiod
  have hres :
      0 < ∑ j ∈ Finset.range h, doublingResidue p v j := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hperiod.1)
    subst h
    rw [Finset.sum_range_succ']
    have hzero := doublingResidue_pos p hv hvodd hpv 0
    omega
  by_contra hw
  have : doublingWrapCount p v h = 0 := Nat.eq_zero_of_not_pos hw
  rw [this, mul_zero] at hsum
  omega

/-- The wrap count is invariant under rotation of a complete residue cycle. -/
theorem doublingWrapCount_mul_pow_eq
    (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (N : ℕ) :
    doublingWrapCount (p * 2 ^ N) v h = doublingWrapCount p v h := by
  have hsum :
      ∑ j ∈ Finset.range h, doublingResidue (p * 2 ^ N) v j =
        ∑ j ∈ Finset.range h, doublingResidue p v j := by
    calc
      ∑ j ∈ Finset.range h, doublingResidue (p * 2 ^ N) v j =
          ∑ j ∈ Finset.range h, doublingResidue p v (N + j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [doublingResidue_add]
      _ = ∑ j ∈ Finset.range h, doublingResidue p v j := by
            apply sum_range_add_eq_sum_range_of_periodic
            intro n
            exact doublingResidue_add_period p hperiod n
  rw [sum_doublingResidue_eq_mul_wrapCount (p * 2 ^ N) hperiod,
    sum_doublingResidue_eq_mul_wrapCount p hperiod] at hsum
  exact Nat.eq_of_mul_eq_mul_left hv hsum

/-! ## One-wrap classification -/

/-- A bit-valued family whose sum is one has one and only one nonzero
position in the displayed range. -/
theorem exists_unique_wrap_of_sum_eq_one
    (h : ℕ) (wrap : ℕ → ℕ)
    (hbit : ∀ j < h, wrap j ≤ 1)
    (hone : ∑ j ∈ Finset.range h, wrap j = 1) :
    ∃ t < h, wrap t = 1 ∧
      ∀ j < h, j ≠ t → wrap j = 0 := by
  let support := (Finset.range h).filter fun j ↦ wrap j = 1
  have hsumcard : ∑ j ∈ Finset.range h, wrap j = support.card := by
    calc
      ∑ j ∈ Finset.range h, wrap j =
          ∑ j ∈ Finset.range h, if wrap j = 1 then 1 else 0 := by
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            have hjbit := hbit j (Finset.mem_range.mp hj)
            by_cases hwrap : wrap j = 1
            · simp [hwrap]
            · have : wrap j = 0 := by omega
              simp [this]
      _ = support.card := by
            change ∑ j ∈ Finset.range h, (if wrap j = 1 then 1 else 0) =
              ((Finset.range h).filter fun j ↦ wrap j = 1).card
            exact
              (Finset.card_filter (fun j ↦ wrap j = 1) (Finset.range h)).symm
  have hcard : support.card = 1 := by omega
  obtain ⟨t, hsupport⟩ := Finset.card_eq_one.mp hcard
  have htmem : t ∈ support := by simp [hsupport]
  have ht : t < h := Finset.mem_range.mp (Finset.mem_filter.mp htmem).1
  have htone : wrap t = 1 := (Finset.mem_filter.mp htmem).2
  refine ⟨t, ht, htone, ?_⟩
  intro j hj hjne
  have hjnot : j ∉ support := by
    rw [hsupport]
    intro hmem
    exact hjne (Finset.mem_singleton.mp hmem)
  have hjnotone : wrap j ≠ 1 := by
    intro hjone
    exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjone⟩)
  have hjbit := hbit j hj
  omega

/-- Binary value represented by a prefix of wrap digits, with the most
recent digit least significant in `E(n+1)=2E(n)+wrap(n)`. -/
def accumulatedWrap (wrap : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * accumulatedWrap wrap n + wrap n

/-- Unroll the binary carry recurrence through a finite prefix. -/
theorem recurrence_unroll
    (v n : ℕ) (r wrap : ℕ → ℕ)
    (hrec : ∀ j < n, 2 * r j = v * wrap j + r (j + 1)) :
    2 ^ n * r 0 = r n + v * accumulatedWrap wrap n := by
  induction n with
  | zero => simp [accumulatedWrap]
  | succ n ih =>
      have ih' := ih (fun j hj ↦ hrec j (Nat.lt_trans hj (Nat.lt_succ_self n)))
      have hn := hrec n (Nat.lt_succ_self n)
      calc
        2 ^ (n + 1) * r 0 = 2 * (2 ^ n * r 0) := by
          rw [pow_succ]
          ring
        _ = 2 * (r n + v * accumulatedWrap wrap n) := by rw [ih']
        _ = 2 * r n + 2 * v * accumulatedWrap wrap n := by ring
        _ = (v * wrap n + r (n + 1)) +
            2 * v * accumulatedWrap wrap n := by rw [hn]
        _ = r (n + 1) +
            v * (2 * accumulatedWrap wrap n + wrap n) := by ring
        _ = r (n + 1) + v * accumulatedWrap wrap (n + 1) := rfl

private theorem accumulatedWrap_eq_zero_of_zero
    (wrap : ℕ → ℕ) (n : ℕ) (hzero : ∀ j < n, wrap j = 0) :
    accumulatedWrap wrap n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [accumulatedWrap,
        ih (fun j hj ↦ hzero j (Nat.lt_trans hj (Nat.lt_succ_self n))),
        hzero n (Nat.lt_succ_self n)]

theorem accumulatedWrap_eq_pow_of_unique
    (wrap : ℕ → ℕ) {h t : ℕ} (ht : t < h)
    (htone : wrap t = 1)
    (hother : ∀ j < h, j ≠ t → wrap j = 0) :
    accumulatedWrap wrap h = 2 ^ (h - 1 - t) := by
  have hprefix : accumulatedWrap wrap t = 0 :=
    accumulatedWrap_eq_zero_of_zero wrap t fun j hj ↦
      hother j (Nat.lt_trans hj ht) (by omega)
  have hafter : ∀ d : ℕ, t + 1 + d ≤ h →
      accumulatedWrap wrap (t + 1 + d) = 2 ^ d := by
    intro d
    induction d with
    | zero =>
        intro _
        rw [show t + 1 + 0 = t + 1 by omega, accumulatedWrap, hprefix, htone]
        simp
    | succ d ih =>
        intro hdle
        have hprev := ih (by omega)
        have hidxlt : t + 1 + d < h := by omega
        have hzero : wrap (t + 1 + d) = 0 :=
          hother (t + 1 + d) hidxlt (by omega)
        rw [show t + 1 + (d + 1) = (t + 1 + d) + 1 by omega,
          accumulatedWrap, hprev, hzero, pow_succ]
        ring
  let d := h - (t + 1)
  have hdle : t + 1 + d ≤ h := by
    dsimp [d]
    omega
  have hdeq : t + 1 + d = h := by
    dsimp [d]
    omega
  have hdexp : d = h - 1 - t := by
    dsimp [d]
    omega
  have hresult := hafter d hdle
  rw [hdeq, hdexp] at hresult
  exact hresult

private theorem two_pow_sub_one_mod_two {h : ℕ} (hh : 0 < h) :
    (2 ^ h - 1) % 2 = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have heq : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
    rw [pow_succ]
    omega
  rw [heq]
  simp [Nat.add_mod]

/-- Full algebraic classification of a one-wrap positive closed cycle.  Its
starting residue is a power of two and its modulus is Mersenne. -/
theorem one_wrap_cycle_classification
    (v h : ℕ) (r wrap : ℕ → ℕ)
    (hh : 0 < h) (hrcop : (r 0).Coprime v)
    (hclosed : r h = r 0)
    (hrec : ∀ j < h, 2 * r j = v * wrap j + r (j + 1))
    (hbit : ∀ j < h, wrap j ≤ 1)
    (hone : ∑ j ∈ Finset.range h, wrap j = 1) :
    v = 2 ^ h - 1 ∧ ∃ a < h, r 0 = 2 ^ a := by
  obtain ⟨t, ht, htone, hother⟩ :=
    exists_unique_wrap_of_sum_eq_one h wrap hbit hone
  let a := h - 1 - t
  have ha : a < h := by
    dsimp [a]
    omega
  have hacc : accumulatedWrap wrap h = 2 ^ a :=
    accumulatedWrap_eq_pow_of_unique wrap ht htone hother
  have hunroll := recurrence_unroll v h r wrap hrec
  rw [hclosed, hacc] at hunroll
  have hpge : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hfactor : (2 ^ h - 1) * r 0 = v * 2 ^ a := by
    apply Nat.add_right_cancel (m := r 0)
    calc
      (2 ^ h - 1) * r 0 + r 0 =
          ((2 ^ h - 1) + 1) * r 0 := by ring
      _ = 2 ^ h * r 0 := by rw [Nat.sub_add_cancel hpge]
      _ = r 0 + v * 2 ^ a := hunroll
      _ = v * 2 ^ a + r 0 := by rw [add_comm]
  have hrdvdprod : r 0 ∣ v * 2 ^ a := by
    refine ⟨2 ^ h - 1, ?_⟩
    simpa [mul_comm] using hfactor.symm
  have hrdvdpow : r 0 ∣ 2 ^ a :=
    hrcop.dvd_of_dvd_mul_left hrdvdprod
  obtain ⟨b, hb, hrpow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrdvdpow
  have hpowa : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hrpow, hpowa] at hfactor
  have hfactor' :
      (2 ^ h - 1) * 2 ^ b = (v * 2 ^ (a - b)) * 2 ^ b := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hfactor
  have hmersen : 2 ^ h - 1 = v * 2 ^ (a - b) :=
    Nat.mul_right_cancel (by positivity) hfactor'
  have hab : a - b = 0 := by
    by_contra hab0
    have hpowmod : 2 ^ (a - b) % 2 = 0 := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hab0
      rw [hd, pow_succ]
      simp
    have hmod := congrArg (fun n : ℕ ↦ n % 2) hmersen
    change (2 ^ h - 1) % 2 = (v * 2 ^ (a - b)) % 2 at hmod
    rw [two_pow_sub_one_mod_two hh, Nat.mul_mod, hpowmod] at hmod
    simp at hmod
  have hba : b = a := by omega
  have hv : v = 2 ^ h - 1 := by
    rw [hab, pow_zero, mul_one] at hmersen
    exact hmersen.symm
  refine ⟨hv, a, ha, ?_⟩
  simpa [hba] using hrpow

/-- Canonical one-wrap theorem: the odd denominator is `2^h-1`, and the
numerator residue lies in the power-of-two orbit. -/
theorem one_doublingWrap_classification
    (p : ℕ) {v h : ℕ} (hv : 1 < v) (_hvodd : Odd v)
    (hpv : p.Coprime v) (hperiod : IsDoublingPeriod v h)
    (hone : doublingWrapCount p v h = 1) :
    v = 2 ^ h - 1 ∧
      ∃ a < h, doublingResidue p v 0 = 2 ^ a := by
  have hrcop : (doublingResidue p v 0).Coprime v := by
    simpa [doublingResidue, Nat.coprime_iff_gcd_eq_one] using hpv
  apply one_wrap_cycle_classification v h
    (doublingResidue p v) (doublingWrapDigit p v)
    hperiod.1 hrcop
  · simpa using doublingResidue_add_period p hperiod 0
  · intro j _
    exact doublingResidue_carry p v j
  · intro j _
    exact doublingWrapDigit_le_one p (by omega) j
  · exact hone

/-! ## The actual multiplicative order of two -/

/-- Mathlib realization of `ord_v(2)` for an odd modulus. -/
noncomputable def oddDoublingOrder (v : ℕ) (hvodd : Odd v) : ℕ :=
  orderOf (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hvodd))

theorem pow_oddDoublingOrder_mod_eq_one
    {v : ℕ} (hv : 1 < v) (hvodd : Odd v) :
    2 ^ oddDoublingOrder v hvodd % v = 1 := by
  let hcop : Nat.Coprime 2 v := Nat.coprime_two_left.mpr hvodd
  let u : (ZMod v)ˣ := ZMod.unitOfCoprime 2 hcop
  have hu : u ^ orderOf u = 1 := pow_orderOf_eq_one u
  have hz := congrArg (fun z : (ZMod v)ˣ ↦ (z : ZMod v)) hu
  change (u : ZMod v) ^ orderOf u = 1 at hz
  have huval : (u : ZMod v) = 2 := by
    simp [u, ZMod.coe_unitOfCoprime]
  rw [huval] at hz
  have hz' : ((2 ^ orderOf u : ℕ) : ZMod v) = ((1 : ℕ) : ZMod v) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hz
  have hmod := (ZMod.natCast_eq_natCast_iff' (2 ^ orderOf u) 1 v).mp hz'
  have horder : oddDoublingOrder v hvodd = orderOf u := by
    simp [oddDoublingOrder, u]
  rw [horder]
  simpa [Nat.mod_eq_of_lt hv] using hmod

theorem oddDoublingOrder_pos {v : ℕ} (hvodd : Odd v) :
    0 < oddDoublingOrder v hvodd := by
  exact orderOf_pos _

/-- The actual multiplicative order closes the canonical residue cycle. -/
theorem oddDoublingOrder_isPeriod
    {v : ℕ} (hv : 1 < v) (hvodd : Odd v) :
    IsDoublingPeriod v (oddDoublingOrder v hvodd) := by
  refine ⟨oddDoublingOrder_pos hvodd, ?_⟩
  have hmod := pow_oddDoublingOrder_mod_eq_one hv hvodd
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hv] using hmod

theorem oddOrder_doublingWrapCount_pos
    (p : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.Coprime v) :
    0 < doublingWrapCount p v (oddDoublingOrder v hvodd) := by
  exact doublingWrapCount_pos p hv hvodd hpv
    (oddDoublingOrder_isPeriod hv hvodd)

/-- The one-wrap classification specialized to the multiplicative order of
two modulo the odd modulus. -/
theorem one_oddOrder_doublingWrap_classification
    (p : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.Coprime v)
    (hone : doublingWrapCount p v (oddDoublingOrder v hvodd) = 1) :
    v = 2 ^ oddDoublingOrder v hvodd - 1 ∧
      ∃ a < oddDoublingOrder v hvodd,
        doublingResidue p v 0 = 2 ^ a := by
  exact one_doublingWrap_classification p hv hvodd hpv
    (oddDoublingOrder_isPeriod hv hvodd) hone

/-! ## Odd-denominator tail states -/

/-- A natural state which is simultaneously the odd-denominator scaling of
the true support tail and the canonical doubling residue of a numerator.
The rational-fraction bridge below constructs this state after removing the
power of two from a displayed denominator. -/
def IsOddSupportTailState
    (A : Set ℕ) (p v : ℕ) (u : ℕ → ℕ) : Prop :=
  (∀ N : ℕ,
      (u N : ℝ) = (v : ℝ) * binaryCoeffTail (supportCoeff A) N) ∧
    (∀ N : ℕ, u N % v = doublingResidue p v N)

/-- Integral excess of an odd tail state above its least residue. -/
def oddTailExcess (u : ℕ → ℕ) (v N : ℕ) : ℕ :=
  u N / v

/-- Exact pointwise decomposition of a genuine odd tail state into its least
residue and a nonnegative integral excess. -/
theorem oddSupportTail_eq_residue_div_add_excess
    (A : Set ℕ) (p : ℕ) {v : ℕ} (hv : 0 < v) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) N =
      (doublingResidue p v N : ℝ) / (v : ℝ) +
        (oddTailExcess u v N : ℝ) := by
  have hdecomp :
      u N = v * oddTailExcess u v N + doublingResidue p v N := by
    rw [oddTailExcess, ← hstate.2 N]
    exact (Nat.div_add_mod (u N) v).symm
  have hdecompR := congrArg (fun x : ℕ ↦ (x : ℝ)) hdecomp
  change (u N : ℝ) =
    (v * oddTailExcess u v N + doublingResidue p v N : ℕ) at hdecompR
  rw [hstate.1 N] at hdecompR
  push_cast at hdecompR
  have hvR : (v : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Exact block identity: a complete residue cycle contributes its wrap
count, and every additional lift of a tail state contributes one nonnegative
integer.  This is the finite algebra behind both the periodic lower bound and
the exact excess-mean identity. -/
theorem sum_supportTail_block_eq_wrapCount_add_excess
    (A : Set ℕ) (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u) (N : ℕ) :
    ∑ j ∈ Finset.range h, binaryCoeffTail (supportCoeff A) (N + j) =
      (doublingWrapCount (p * 2 ^ N) v h : ℝ) +
        ∑ j ∈ Finset.range h, (oddTailExcess u v (N + j) : ℝ) := by
  calc
    ∑ j ∈ Finset.range h, binaryCoeffTail (supportCoeff A) (N + j) =
        ∑ j ∈ Finset.range h,
          ((doublingResidue (p * 2 ^ N) v j : ℝ) / (v : ℝ) +
            (oddTailExcess u v (N + j) : ℝ)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [← doublingResidue_add]
              exact oddSupportTail_eq_residue_div_add_excess
                A p hv u hstate (N + j)
    _ = ((∑ j ∈ Finset.range h,
            (doublingResidue (p * 2 ^ N) v j : ℝ)) / (v : ℝ)) +
          ∑ j ∈ Finset.range h,
            (oddTailExcess u v (N + j) : ℝ) := by
              rw [Finset.sum_add_distrib, Finset.sum_div]
    _ = (doublingWrapCount (p * 2 ^ N) v h : ℝ) +
          ∑ j ∈ Finset.range h,
            (oddTailExcess u v (N + j) : ℝ) := by
              rw [← Nat.cast_sum,
                sum_doublingResidue_eq_mul_wrapCount (p * 2 ^ N) hperiod]
              push_cast
              field_simp

/-- Dropping the nonnegative excess terms gives the order-sensitive local
block lower bound. -/
theorem wrapCount_le_sum_supportTail_block
    (A : Set ℕ) (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u) (N : ℕ) :
    (doublingWrapCount (p * 2 ^ N) v h : ℝ) ≤
      ∑ j ∈ Finset.range h,
        binaryCoeffTail (supportCoeff A) (N + j) := by
  rw [sum_supportTail_block_eq_wrapCount_add_excess
    A p hv hperiod u hstate N]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)

/-! ## Rational fractions construct the odd tail state -/

/-- A nonempty positive support forces the numerator of every displayed
positive-denominator fraction to be positive. -/
theorem numerator_pos_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    0 < p := by
  have hseries : 0 < erdosSupportSeries 2 A := by
    rw [erdosSupportSeries_two_eq_binaryCoeffSeries A,
      ← binaryCoeffTail_zero]
    exact binaryCoeffTail_supportCoeff_pos_of_exists_pos_mem A hA 0
  rw [hvalue] at hseries
  have hden : (0 : ℝ) < ((2 ^ c * v : ℕ) : ℝ) := by
    positivity
  rcases (div_pos_iff.mp hseries) with h | h
  · exact_mod_cast h.1
  · linarith

/-- Removing the power-of-two part of a displayed denominator gives a
positive integer state equal to `v` times the shifted true tail.  The state
also carries the exact additive recurrence and its numerator residue class. -/
theorem exists_shifted_odd_tail_states_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℤ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) =
        2 * u n - (v : ℤ) * (supportCoeff A (c + n + 1) : ℤ)) ∧
      (∀ n : ℕ, u n ≡ (2 : ℤ) ^ n * p [ZMOD (v : ℤ)]) := by
  let z : ℕ → ℤ := fun N ↦
    Classical.choose
      (bpow_mul_coeff_series_eq_int_add_tail 2 N (supportCoeff A)
        (by norm_num) (supportCoeff_le_self A))
  have hz : ∀ N : ℕ,
      (2 : ℝ) ^ N * binaryCoeffSeries (supportCoeff A) =
        (z N : ℝ) + binaryCoeffTail (supportCoeff A) N := by
    intro N
    exact Classical.choose_spec
      (bpow_mul_coeff_series_eq_int_add_tail 2 N (supportCoeff A)
        (by norm_num) (supportCoeff_le_self A))
  let u : ℕ → ℤ := fun n ↦
    (2 : ℤ) ^ n * p - (v : ℤ) * z (c + n)
  have hutail : ∀ n : ℕ, (u n : ℝ) =
      (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n) := by
    intro n
    have hN := hz (c + n)
    rw [← erdosSupportSeries_two_eq_binaryCoeffSeries A, hvalue] at hN
    have hmul := congrArg (fun x : ℝ ↦ (v : ℝ) * x) hN
    change
      (v : ℝ) *
          ((2 : ℝ) ^ (c + n) *
            ((p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))) =
        (v : ℝ) *
          ((z (c + n) : ℝ) +
            binaryCoeffTail (supportCoeff A) (c + n)) at hmul
    have hcancel :
        (v : ℝ) *
            ((2 : ℝ) ^ (c + n) *
              ((p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))) =
          (2 : ℝ) ^ n * (p : ℝ) := by
      push_cast
      field_simp
      ring
    rw [hcancel] at hmul
    unfold u
    push_cast
    linarith
  refine ⟨u, hutail, ?_, ?_, ?_⟩
  · intro n
    have htail :=
      binaryCoeffTail_supportCoeff_pos_of_exists_pos_mem A hA (c + n)
    have hreal : (0 : ℝ) < (u n : ℝ) := by
      rw [hutail n]
      positivity
    exact_mod_cast hreal
  · intro n
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [hutail (n + 1), hutail n]
    rw [show c + (n + 1) = (c + n) + 1 by omega,
      binaryCoeffTail_succ (supportCoeff A) (supportCoeff_le_self A) (c + n)]
    ring
  · intro n
    apply Int.modEq_iff_dvd.mpr
    refine ⟨z (c + n), ?_⟩
    unfold u
    ring

/-- Natural-number form of the shifted odd tail state. -/
theorem exists_shifted_odd_tail_nat_states_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) := by
  obtain ⟨uZ, htail, hpos, hrec, hmod⟩ :=
    exists_shifted_odd_tail_states_of_support_fraction
      A hA p c v hv hvalue
  have hp : 0 < p :=
    numerator_pos_of_support_fraction A hA p c v hv hvalue
  let u : ℕ → ℕ := fun n ↦ (uZ n).toNat
  have hu_cast : ∀ n : ℕ, (u n : ℤ) = uZ n := by
    intro n
    simp only [u, Int.toNat_of_nonneg (le_of_lt (hpos n))]
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [← htail n]
    exact_mod_cast hu_cast n
  · intro n
    have hpos' : (0 : ℤ) < (u n : ℤ) := by
      rw [hu_cast n]
      exact hpos n
    exact_mod_cast hpos'
  · intro n
    have hz := hrec n
    have hz' : uZ (n + 1) +
        (v : ℤ) * (supportCoeff A (c + n + 1) : ℤ) =
          2 * uZ n := by
      linarith
    have hz'' : (u (n + 1) : ℤ) +
        (v : ℤ) * (supportCoeff A (c + n + 1) : ℤ) =
          2 * (u n : ℤ) := by
      rw [hu_cast (n + 1), hu_cast n]
      exact hz'
    exact_mod_cast hz''
  · intro n
    have hp_cast : (p.toNat : ℤ) = p :=
      Int.toNat_of_nonneg (le_of_lt hp)
    have hz : (u n : ℤ) ≡
        ((p.toNat * 2 ^ n : ℕ) : ℤ) [ZMOD (v : ℤ)] := by
      rw [hu_cast n, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hp_cast,
        mul_comm]
      exact hmod n
    exact Int.natCast_modEq_iff.mp hz

/-- Any shifted natural tail state with the correct numerator congruence
inherits the canonical wrap-count lower bound on every complete block. -/
theorem wrapCount_le_sum_tail_of_modEq
    (coeff : ℕ → ℕ) (shift p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (htail : ∀ n : ℕ, (u n : ℝ) =
      (v : ℝ) * binaryCoeffTail coeff (shift + n))
    (hmod : ∀ n : ℕ, u n ≡ p * 2 ^ n [MOD v]) (N : ℕ) :
    (doublingWrapCount (p * 2 ^ N) v h : ℝ) ≤
      ∑ j ∈ Finset.range h,
        binaryCoeffTail coeff (shift + (N + j)) := by
  have hblock : v * doublingWrapCount (p * 2 ^ N) v h ≤
      ∑ j ∈ Finset.range h, u (N + j) := by
    rw [← sum_doublingResidue_eq_mul_wrapCount (p * 2 ^ N) hperiod]
    apply Finset.sum_le_sum
    intro j hj
    have hjmod := hmod (N + j)
    have hjmod' : u (N + j) ≡ (p * 2 ^ N) * 2 ^ j [MOD v] := by
      simpa [pow_add, mul_assoc] using hjmod
    change doublingResidue (p * 2 ^ N) v j ≤ u (N + j)
    unfold doublingResidue
    rw [← hjmod']
    exact Nat.mod_le _ _
  have hblockR : (v : ℝ) *
      (doublingWrapCount (p * 2 ^ N) v h : ℝ) ≤
        ∑ j ∈ Finset.range h, (u (N + j) : ℝ) := by
    exact_mod_cast hblock
  have hsum : (∑ j ∈ Finset.range h, (u (N + j) : ℝ)) =
      (v : ℝ) * ∑ j ∈ Finset.range h,
        binaryCoeffTail coeff (shift + (N + j)) := by
    calc
      (∑ j ∈ Finset.range h, (u (N + j) : ℝ)) =
          ∑ j ∈ Finset.range h,
            (v : ℝ) * binaryCoeffTail coeff (shift + (N + j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact htail (N + j)
      _ = (v : ℝ) * ∑ j ∈ Finset.range h,
          binaryCoeffTail coeff (shift + (N + j)) := by
            rw [Finset.mul_sum]
  rw [hsum] at hblockR
  have hvR : (0 : ℝ) < (v : ℝ) := by positivity
  nlinarith

/-- Fraction-facing local order-wrap theorem.  The only normalization here
is the explicit denominator `2^c*v`; reducedness and oddness enter the order
corollary below. -/
theorem support_fraction_wrapCount_le_tail_block
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c : ℕ) {v h : ℕ} (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hperiod : IsDoublingPeriod v h) (N : ℕ) :
    (doublingWrapCount (p.toNat * 2 ^ N) v h : ℝ) ≤
      ∑ j ∈ Finset.range h,
        binaryCoeffTail (supportCoeff A) (c + (N + j)) := by
  obtain ⟨u, htail, _, _, hmod⟩ :=
    exists_shifted_odd_tail_nat_states_of_support_fraction
      A hA p c v hv hvalue
  exact wrapCount_le_sum_tail_of_modEq
    (supportCoeff A) c p.toNat hv hperiod u htail hmod N

/-! ## Reciprocal mass and Cesàro order bounds -/

/-- The reciprocal summand of a support, with exponent zero harmlessly
normalized to zero by real division. -/
noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a

/-- The reciprocal mass `ρ(A) = ∑_{a∈A} 1/a`. -/
noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a

/-- Extended-real-free statement of a reciprocal-mass lower bound: either
the reciprocal family diverges, in which case every finite lower bound is
automatic, or its real tsum is at least `r`. -/
def ReciprocalMassDivergesOrAtLeast (A : Set ℕ) (r : ℝ) : Prop :=
  ¬ Summable (reciprocalSupportTerm A) ∨ r ≤ reciprocalMass A

/-- The finite divisor frequency of `a` in the first `N` positive integers. -/
noncomputable def divisorFrequency (A : Set ℕ) (N a : ℕ) : ℝ :=
  Set.indicator A
    (fun a : ℕ => ((N / a : ℕ) : ℝ) / (N : ℝ)) a

/-- Exact finite double counting: summing the support coefficient through
`N` is the sum of the counts `⌊N/a⌋` over the support. -/
theorem sum_supportCoeff_range_eq_sum_div (A : Set ℕ) (N : ℕ) :
    ∑ n ∈ Finset.range N, supportCoeff A (n + 1) =
      ∑ a ∈ Finset.range (N + 1),
        Set.indicator A (fun a : ℕ => N / a) a := by
  classical
  calc
    ∑ n ∈ Finset.range N, supportCoeff A (n + 1) =
        ∑ n ∈ Finset.range N,
          ∑ a ∈ Finset.range (N + 1),
            if a ∈ A ∧ a ∣ n + 1 then 1 else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnlt : n < N := Finset.mem_range.mp hn
      rw [supportCoeff_eq_card_filter]
      have hfilter :
          ((n + 1).divisors.filter fun a => a ∈ A) =
            ((Finset.range (N + 1)).filter fun a => a ∈ A ∧ a ∣ n + 1) := by
        ext a
        simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_range]
        constructor
        · rintro ⟨⟨hadvd, hn1⟩, haA⟩
          have hale : a ≤ n + 1 := Nat.le_of_dvd (by omega) hadvd
          exact ⟨by omega, haA, hadvd⟩
        · rintro ⟨haN, haA, hadvd⟩
          exact ⟨⟨hadvd, by omega⟩, haA⟩
      rw [hfilter, Finset.card_filter]
    _ = ∑ a ∈ Finset.range (N + 1),
          ∑ n ∈ Finset.range N,
            if a ∈ A ∧ a ∣ n + 1 then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.range (N + 1),
          Set.indicator A (fun a : ℕ => N / a) a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases haA : a ∈ A
      · simp only [haA, true_and]
        rw [← Finset.card_filter]
        simpa [Set.indicator_of_mem haA] using Nat.card_multiples N a
      · simp [haA]

theorem tendsto_nat_div_frequency (a : ℕ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => ((N / a : ℕ) : ℝ) / (N : ℝ)) atTop
      (nhds ((1 : ℝ) / (a : ℝ))) := by
  let rem : ℕ → ℝ := fun N =>
    ((N % a : ℕ) : ℝ) / ((a : ℝ) * (N : ℝ))
  have hrem_nonneg : ∀ N : ℕ, 0 ≤ rem N := by
    intro N
    exact div_nonneg (by positivity) (by positivity)
  have hrem_le : ∀ N : ℕ, rem N ≤ ((N : ℝ)⁻¹) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [rem]
    · have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
      have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
      have hmod : ((N % a : ℕ) : ℝ) / (a : ℝ) ≤ 1 := by
        rw [div_le_one haR]
        exact_mod_cast (Nat.mod_lt N ha).le
      calc
        rem N = (((N % a : ℕ) : ℝ) / (a : ℝ)) * (N : ℝ)⁻¹ := by
          simp only [rem]
          field_simp
        _ ≤ 1 * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hmod hN0
        _ = (N : ℝ)⁻¹ := one_mul _
  have hrem : Tendsto rem atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall hrem_nonneg)
      (Filter.Eventually.of_forall hrem_le)
    exact tendsto_inv_atTop_nhds_zero_nat
  have hformula : ∀ᶠ N : ℕ in atTop,
      ((N / a : ℕ) : ℝ) / (N : ℝ) = (1 : ℝ) / (a : ℝ) - rem N := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNne : (N : ℝ) ≠ 0 := by positivity
    have hane : (a : ℝ) ≠ 0 := by positivity
    have hdivmod :
        (a : ℝ) * ((N / a : ℕ) : ℝ) + ((N % a : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast Nat.div_add_mod N a
    simp only [rem]
    field_simp
    linarith
  have hconst :
      Tendsto (fun _ : ℕ => (1 : ℝ) / (a : ℝ)) atTop
        (nhds ((1 : ℝ) / (a : ℝ))) := tendsto_const_nhds
  have hsub :
      Tendsto (fun N : ℕ => (1 : ℝ) / (a : ℝ) - rem N) atTop
        (nhds ((1 : ℝ) / (a : ℝ))) := by
    simpa using hconst.sub hrem
  exact hsub.congr' (hformula.mono fun _ h => h.symm)

theorem tendsto_divisorFrequency (A : Set ℕ) (a : ℕ) :
    Tendsto (fun N : ℕ => divisorFrequency A N a) atTop
      (nhds (reciprocalSupportTerm A a)) := by
  classical
  by_cases haA : a ∈ A
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [divisorFrequency, reciprocalSupportTerm, haA]
    · simpa [divisorFrequency, reciprocalSupportTerm, haA] using
        tendsto_nat_div_frequency a ha
  · simp [divisorFrequency, reciprocalSupportTerm, haA]

theorem norm_divisorFrequency_le_reciprocalSupportTerm
    (A : Set ℕ) (N a : ℕ) :
    ‖divisorFrequency A N a‖ ≤ reciprocalSupportTerm A a := by
  classical
  by_cases haA : a ∈ A
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [divisorFrequency, reciprocalSupportTerm, haA]
    · rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp [divisorFrequency, reciprocalSupportTerm, haA]
      · have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hnonneg :
            0 ≤ ((N / a : ℕ) : ℝ) / (N : ℝ) := by positivity
        simp only [divisorFrequency, reciprocalSupportTerm,
          Set.indicator_of_mem haA, Real.norm_eq_abs,
          abs_of_nonneg hnonneg]
        rw [div_le_iff₀ hNreal]
        have hcast : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / (a : ℝ) :=
          Nat.cast_div_le
        calc
          ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / (a : ℝ) := hcast
          _ = (1 / (a : ℝ)) * (N : ℝ) := by ring
  · simp [divisorFrequency, reciprocalSupportTerm, haA]

/-- The frequency tsum is exactly the Cesàro mean of `supportCoeff`. -/
theorem tsum_divisorFrequency_eq_supportCoeff_mean (A : Set ℕ) (N : ℕ) :
    ∑' a : ℕ, divisorFrequency A N a =
      ((∑ n ∈ Finset.range N, supportCoeff A (n + 1) : ℕ) : ℝ) / (N : ℝ) := by
  classical
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · rw [sum_supportCoeff_range_eq_sum_div]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases haA : a ∈ A <;>
      simp [divisorFrequency, haA]
  · intro a haN
    rw [Finset.mem_range, not_lt] at haN
    have hdiv : N / a = 0 := Nat.div_eq_of_lt (by omega)
    simp [divisorFrequency, hdiv]

/-- If the reciprocal support terms are summable, the Cesàro mean of the
divisor-count coefficients tends to `reciprocalMass A`. -/
theorem tendsto_supportCoeff_mean_reciprocalMass
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A)) :
    Tendsto
      (fun N : ℕ =>
        ((∑ n ∈ Finset.range N, supportCoeff A (n + 1) : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (reciprocalMass A)) := by
  have htannery :
      Tendsto (fun N : ℕ => ∑' a : ℕ, divisorFrequency A N a) atTop
        (nhds (∑' a : ℕ, reciprocalSupportTerm A a)) :=
    tendsto_tsum_of_dominated_convergence hsum
      (tendsto_divisorFrequency A)
      (Filter.Eventually.of_forall
        (norm_divisorFrequency_le_reciprocalSupportTerm A))
  simpa only [tsum_divisorFrequency_eq_supportCoeff_mean, reciprocalMass]
    using htannery

/-- A ready-to-use lower-bound corollary: any eventual lower bound on the
support-coefficient Cesàro means is inherited by reciprocal mass. -/
theorem le_reciprocalMass_of_eventually_le_supportCoeff_mean
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A)) (r : ℝ)
    (hr : ∀ᶠ N : ℕ in atTop,
      r ≤ ((∑ n ∈ Finset.range N, supportCoeff A (n + 1) : ℕ) : ℝ) / (N : ℝ)) :
    r ≤ reciprocalMass A :=
  ge_of_tendsto (tendsto_supportCoeff_mean_reciprocalMass A hsum) hr

/-- Cesàro mean of a real sequence over indices `0,...,N-1`. -/
noncomputable def cesaroMean (x : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, x n) / (N : ℝ)

/-- Finite telescoping of the binary-tail recurrence. -/
theorem sum_supportCoeff_cast_eq_sum_binaryCoeffTail_add_boundary
    (A : Set ℕ) (N : ℕ) :
    ((∑ n ∈ Finset.range N, supportCoeff A (n + 1) : ℕ) : ℝ) =
      (∑ n ∈ Finset.range N, binaryCoeffTail (supportCoeff A) n) +
        binaryCoeffTail (supportCoeff A) 0 -
          binaryCoeffTail (supportCoeff A) N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ, Nat.cast_add, ih]
      rw [binaryCoeffTail_succ
        (supportCoeff A) (supportCoeff_le_self A) N]
      ring

theorem tendsto_sqrt_nat_div_nat_zero :
    Tendsto (fun N : ℕ => Real.sqrt (N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
  have hsqrtTop :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrtTop
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hsqrtne : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (by positivity)
  calc
    (Real.sqrt (N : ℝ))⁻¹ =
        Real.sqrt (N : ℝ) / Real.sqrt (N : ℝ) ^ 2 := by field_simp
    _ = Real.sqrt (N : ℝ) / (N : ℝ) :=
      congrArg (fun x : ℝ => Real.sqrt (N : ℝ) / x) hsq

theorem tendsto_binaryCoeffTail_supportCoeff_div_nat_zero (A : Set ℕ) :
    Tendsto
      (fun N : ℕ => binaryCoeffTail (supportCoeff A) N / (N : ℝ))
      atTop (nhds 0) := by
  have hinvNat : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hupper :
      Tendsto
        (fun N : ℕ =>
          (2 * Real.sqrt (N : ℝ) + 4) / (N : ℝ))
        atTop (nhds 0) := by
    have h := (tendsto_sqrt_nat_div_nat_zero.const_mul 2).add
      (hinvNat.const_mul 4)
    simpa only [mul_zero, add_zero] using
      h.congr' (Filter.Eventually.of_forall fun N => by ring)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N =>
      div_nonneg (binaryCoeffTail_nonneg (supportCoeff A) N) (by positivity))
    (Filter.Eventually.of_forall fun N =>
      div_le_div_of_nonneg_right
        (binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A N)
        (by positivity))
    hupper

/-- The Cesàro mean of the scaled binary support tails has the same limit as
the coefficient mean, namely `reciprocalMass A`.  A rational tail state can
then be decomposed into a periodic residue fraction and a nonnegative integer
excess. -/
theorem tendsto_binaryCoeffTail_supportCoeff_mean_reciprocalMass
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A)) :
    Tendsto (cesaroMean (binaryCoeffTail (supportCoeff A))) atTop
      (nhds (reciprocalMass A)) := by
  have hcoeff := tendsto_supportCoeff_mean_reciprocalMass A hsum
  have hconstDiv :
      Tendsto
        (fun N : ℕ =>
          binaryCoeffTail (supportCoeff A) 0 / (N : ℝ))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_nhds_zero_nat.const_mul
        (binaryCoeffTail (supportCoeff A) 0))
  have hboundary :
      Tendsto
        (fun N : ℕ =>
          (binaryCoeffTail (supportCoeff A) 0 -
            binaryCoeffTail (supportCoeff A) N) / (N : ℝ))
        atTop (nhds 0) := by
    simpa only [sub_div, sub_zero] using
      hconstDiv.sub (tendsto_binaryCoeffTail_supportCoeff_div_nat_zero A)
  have hlim := hcoeff.sub hboundary
  simpa only [sub_zero] using hlim.congr'
    (Filter.Eventually.of_forall fun N => by
      rw [cesaroMean]
      have hfinite :=
        sum_supportCoeff_cast_eq_sum_binaryCoeffTail_add_boundary A N
      linear_combination hfinite / (N : ℝ))

theorem le_reciprocalMass_of_eventually_le_binaryCoeffTail_mean
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A)) (r : ℝ)
    (hr : ∀ᶠ N : ℕ in atTop,
      r ≤ cesaroMean (binaryCoeffTail (supportCoeff A)) N) :
    r ≤ reciprocalMass A :=
  ge_of_tendsto
    (tendsto_binaryCoeffTail_supportCoeff_mean_reciprocalMass A hsum) hr

/-- Exact partition of a prefix of length `M*h` into `M` consecutive
blocks of length `h`. -/
theorem sum_range_mul_eq_sum_blocks (x : ℕ → ℝ) (M h : ℕ) :
    ∑ n ∈ Finset.range (M * h), x n =
      ∑ q ∈ Finset.range M, ∑ j ∈ Finset.range h, x (q * h + j) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

/-- A uniform lower bound `w` on every length-`h` block forces the
Cesàro limit to be at least `w/h`. -/
theorem div_le_of_tendsto_cesaroMean_of_block_lower_bound
    (x : ℕ → ℝ) (limit : ℝ) (h w : ℕ) (hh : 0 < h)
    (hlimit : Tendsto (cesaroMean x) atTop (nhds limit))
    (hblock : ∀ q : ℕ,
      (w : ℝ) ≤ ∑ j ∈ Finset.range h, x (q * h + j)) :
    (w : ℝ) / (h : ℝ) ≤ limit := by
  have htotal : ∀ M : ℕ,
      (M : ℝ) * (w : ℝ) ≤ ∑ n ∈ Finset.range (M * h), x n := by
    intro M
    calc
      (M : ℝ) * (w : ℝ) = ∑ q ∈ Finset.range M, (w : ℝ) := by simp
      _ ≤ ∑ q ∈ Finset.range M,
          ∑ j ∈ Finset.range h, x (q * h + j) :=
        Finset.sum_le_sum fun q _ => hblock q
      _ = ∑ n ∈ Finset.range (M * h), x n :=
        (sum_range_mul_eq_sum_blocks x M h).symm
  have hmean : ∀ M : ℕ, 0 < M →
      (w : ℝ) / (h : ℝ) ≤ cesaroMean x (M * h) := by
    intro M hM
    rw [cesaroMean, le_div_iff₀ (by positivity : (0 : ℝ) < (M * h : ℕ))]
    calc
      (w : ℝ) / (h : ℝ) * (↑(M * h) : ℝ) =
          (M : ℝ) * (w : ℝ) := by
        push_cast
        field_simp
      _ ≤ ∑ n ∈ Finset.range (M * h), x n := htotal M
  have hmulTop : Tendsto (fun M : ℕ => M * h) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    exact (eventually_ge_atTop b).mono fun M hMb => by
      exact hMb.trans (Nat.le_mul_of_pos_right M hh)
  exact ge_of_tendsto (hlimit.comp hmulTop)
    ((eventually_gt_atTop (0 : ℕ)).mono fun M hM => hmean M hM)

/-- A lower bound `w` on every length-`h` block of support tails yields
`reciprocalMass A ≥ w / h`. -/
theorem wrapRatio_le_reciprocalMass_of_binaryCoeffTail_blocks
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (h w : ℕ) (hh : 0 < h)
    (hblock : ∀ q : ℕ,
      (w : ℝ) ≤ ∑ j ∈ Finset.range h,
        binaryCoeffTail (supportCoeff A) (q * h + j)) :
    (w : ℝ) / (h : ℝ) ≤ reciprocalMass A :=
  div_le_of_tendsto_cesaroMean_of_block_lower_bound
    (binaryCoeffTail (supportCoeff A)) (reciprocalMass A) h w hh
    (tendsto_binaryCoeffTail_supportCoeff_mean_reciprocalMass A hsum)
    hblock

/-- The incomplete final block after the `N / h` complete aligned blocks. -/
noncomputable def blockRemainder (x : ℕ → ℝ) (h N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N % h), x ((N / h) * h + j)

theorem sum_range_eq_mul_blockSum_add_blockRemainder
    (x : ℕ → ℝ) (h : ℕ) (blockSum : ℝ)
    (hblock : ∀ q : ℕ,
      ∑ j ∈ Finset.range h, x (q * h + j) = blockSum)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, x n =
      ((N / h : ℕ) : ℝ) * blockSum + blockRemainder x h N := by
  have hlen : (N / h) * h + N % h = N := by
    simpa [mul_comm] using Nat.div_add_mod N h
  calc
    ∑ n ∈ Finset.range N, x n =
        ∑ n ∈ Finset.range ((N / h) * h + N % h), x n := by rw [hlen]
    _ = (∑ n ∈ Finset.range ((N / h) * h), x n) +
          blockRemainder x h N := by
      rw [Finset.sum_range_add]
      rfl
    _ = (∑ q ∈ Finset.range (N / h),
          ∑ j ∈ Finset.range h, x (q * h + j)) +
          blockRemainder x h N := by
      rw [sum_range_mul_eq_sum_blocks]
    _ = ((N / h : ℕ) : ℝ) * blockSum + blockRemainder x h N := by
      rw [Finset.sum_congr rfl fun q _ => hblock q]
      simp

theorem blockRemainder_nonneg
    (x : ℕ → ℝ) (hx0 : ∀ n : ℕ, 0 ≤ x n) (h N : ℕ) :
    0 ≤ blockRemainder x h N :=
  Finset.sum_nonneg fun j _ => hx0 ((N / h) * h + j)

theorem blockRemainder_le_period
    (x : ℕ → ℝ) (hx1 : ∀ n : ℕ, x n ≤ 1)
    {h : ℕ} (hh : 0 < h) (N : ℕ) :
    blockRemainder x h N ≤ (h : ℝ) := by
  calc
    blockRemainder x h N ≤ ∑ _j ∈ Finset.range (N % h), (1 : ℝ) :=
      Finset.sum_le_sum fun j _ => hx1 ((N / h) * h + j)
    _ = (N % h : ℕ) := by simp
    _ ≤ (h : ℝ) := by exact_mod_cast (Nat.mod_lt N hh).le

/-- A nonnegative sequence bounded by one and having the same exact sum on
every aligned length-`h` block has Cesàro mean `blockSum / h`. -/
theorem tendsto_cesaroMean_of_constant_blocks
    (x : ℕ → ℝ) (h : ℕ) (blockSum : ℝ) (hh : 0 < h)
    (hx0 : ∀ n : ℕ, 0 ≤ x n) (hx1 : ∀ n : ℕ, x n ≤ 1)
    (hblock : ∀ q : ℕ,
      ∑ j ∈ Finset.range h, x (q * h + j) = blockSum) :
    Tendsto (cesaroMean x) atTop (nhds (blockSum / (h : ℝ))) := by
  have hbase0 := (tendsto_nat_div_frequency h hh).mul_const blockSum
  have hbase :
      Tendsto
        (fun N : ℕ =>
          ((N / h : ℕ) : ℝ) * blockSum / (N : ℝ))
        atTop (nhds (blockSum / (h : ℝ))) := by
    convert hbase0 using 1
    · funext N
      ring
    · ring_nf
  have hupper :
      Tendsto (fun N : ℕ => (h : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_nhds_zero_nat.const_mul (h : ℝ))
  have hrem :
      Tendsto (fun N : ℕ => blockRemainder x h N / (N : ℝ))
        atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun N =>
        div_nonneg (blockRemainder_nonneg x hx0 h N) (by positivity))
      (Filter.Eventually.of_forall fun N =>
        div_le_div_of_nonneg_right (blockRemainder_le_period x hx1 hh N)
          (by positivity))
      hupper
  have hsum := hbase.add hrem
  simpa only [add_zero] using hsum.congr'
    (Filter.Eventually.of_forall fun N => by
      rw [cesaroMean,
        sum_range_eq_mul_blockSum_add_blockRemainder x h blockSum hblock N]
      ring)

/-- If each tail is a periodic residue contribution plus an excess, the
excess Cesàro mean converges automatically to `ρ(A) - residueMean`. -/
theorem tendsto_cesaroMean_excess_of_binaryCoeffTail_decomposition
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (residue excess : ℕ → ℝ) (residueMean : ℝ)
    (hdecomp : ∀ N : ℕ,
      binaryCoeffTail (supportCoeff A) N = residue N + excess N)
    (hresidue : Tendsto (cesaroMean residue) atTop (nhds residueMean)) :
    Tendsto (cesaroMean excess) atTop
      (nhds (reciprocalMass A - residueMean)) := by
  have hlim :=
    (tendsto_binaryCoeffTail_supportCoeff_mean_reciprocalMass A hsum).sub
      hresidue
  simpa only using hlim.congr'
    (Filter.Eventually.of_forall fun N => by
      simp only [cesaroMean, ← sub_div, ← Finset.sum_sub_distrib]
      refine congrArg (fun x : ℝ => x / (N : ℝ)) ?_
      refine Finset.sum_congr rfl fun n _ => ?_
      linarith [hdecomp n])

/-- Direct wrap lower bound: a nonnegative tail excess over a residue word
of Cesàro mean `r` forces `ρ(A) ≥ r`. -/
theorem residueMean_le_reciprocalMass_of_binaryCoeffTail_decomposition
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (residue excess : ℕ → ℝ) (residueMean : ℝ)
    (hdecomp : ∀ N : ℕ,
      binaryCoeffTail (supportCoeff A) N = residue N + excess N)
    (hexcess : ∀ N : ℕ, 0 ≤ excess N)
    (hresidue : Tendsto (cesaroMean residue) atTop (nhds residueMean)) :
    residueMean ≤ reciprocalMass A := by
  have hexcessMean :=
    tendsto_cesaroMean_excess_of_binaryCoeffTail_decomposition
      A hsum residue excess residueMean hdecomp hresidue
  have hnonneg : 0 ≤ reciprocalMass A - residueMean :=
    ge_of_tendsto hexcessMean
      (Filter.Eventually.of_forall fun N =>
        div_nonneg (Finset.sum_nonneg fun n _ => hexcess n) (by positivity))
  linarith

/-- Exact `ρ = residueMean + lim-mean(excess)` identity when the excess
mean is named explicitly. -/
theorem reciprocalMass_eq_residueMean_add_excessMean
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (residue excess : ℕ → ℝ) (residueMean excessMean : ℝ)
    (hdecomp : ∀ N : ℕ,
      binaryCoeffTail (supportCoeff A) N = residue N + excess N)
    (hresidue : Tendsto (cesaroMean residue) atTop (nhds residueMean))
    (hexcess : Tendsto (cesaroMean excess) atTop (nhds excessMean)) :
    reciprocalMass A = residueMean + excessMean := by
  have hsumMean := hresidue.add hexcess
  have htailMean :
      Tendsto (cesaroMean (binaryCoeffTail (supportCoeff A))) atTop
        (nhds (residueMean + excessMean)) := by
    apply hsumMean.congr'
    exact Filter.Eventually.of_forall fun N => by
      simp only [cesaroMean]
      rw [← add_div]
      refine congrArg (fun x : ℝ => x / (N : ℝ)) ?_
      rw [← Finset.sum_add_distrib]
      exact (Finset.sum_congr rfl fun n _ => hdecomp n).symm
  exact tendsto_nhds_unique
    (tendsto_binaryCoeffTail_supportCoeff_mean_reciprocalMass A hsum)
    htailMean

theorem doublingResidue_mul_period
    (p : ℕ) {v h : ℕ} (hperiod : IsDoublingPeriod v h)
    (q n : ℕ) :
    doublingResidue (p * 2 ^ (q * h)) v n = doublingResidue p v n := by
  have hper : Function.Periodic (doublingResidue p v) h :=
    doublingResidue_add_period p hperiod
  calc
    doublingResidue (p * 2 ^ (q * h)) v n =
        doublingResidue p v (q * h + n) :=
      (doublingResidue_add p v (q * h) n).symm
    _ = doublingResidue p v (n + q * h) := by rw [add_comm]
    _ = doublingResidue p v n := (hper.nat_mul q) n

theorem doublingWrapCount_mul_period
    (p : ℕ) {v h : ℕ} (hperiod : IsDoublingPeriod v h)
    (q : ℕ) :
    doublingWrapCount (p * 2 ^ (q * h)) v h =
      doublingWrapCount p v h := by
  unfold doublingWrapCount doublingWrapDigit
  exact Finset.sum_congr rfl fun n _ => by
    rw [doublingResidue_mul_period p hperiod q n]

theorem tendsto_cesaroMean_normalizedDoublingResidue
    (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) :
    Tendsto
      (cesaroMean (fun N : ℕ =>
        (doublingResidue p v N : ℝ) / (v : ℝ)))
      atTop
      (nhds ((doublingWrapCount p v h : ℝ) / (h : ℝ))) := by
  apply tendsto_cesaroMean_of_constant_blocks
    (fun N : ℕ => (doublingResidue p v N : ℝ) / (v : ℝ))
    h (doublingWrapCount p v h : ℝ) hperiod.1
  · intro N
    positivity
  · intro N
    rw [div_le_one (by positivity : (0 : ℝ) < (v : ℝ))]
    exact_mod_cast (doublingResidue_lt p hv N).le
  · intro q
    calc
      ∑ j ∈ Finset.range h,
          (doublingResidue p v (q * h + j) : ℝ) / (v : ℝ) =
          ∑ j ∈ Finset.range h,
            (doublingResidue p v j : ℝ) / (v : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [doublingResidue_add,
          doublingResidue_mul_period p hperiod q j]
      _ = (doublingWrapCount p v h : ℝ) := by
        rw [← Finset.sum_div, ← Nat.cast_sum,
          sum_doublingResidue_eq_mul_wrapCount p hperiod]
        push_cast
        field_simp

/-- The Cesàro mean of the odd-tail excess exists and equals
`reciprocalMass A - doublingWrapCount p v h / h`. -/
theorem tendsto_oddTailExcess_mean
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u) :
    Tendsto
      (cesaroMean (fun N : ℕ => (oddTailExcess u v N : ℝ)))
      atTop
      (nhds (reciprocalMass A -
        (doublingWrapCount p v h : ℝ) / (h : ℝ))) := by
  apply tendsto_cesaroMean_excess_of_binaryCoeffTail_decomposition
    A hsum
    (fun N : ℕ => (doublingResidue p v N : ℝ) / (v : ℝ))
    (fun N : ℕ => (oddTailExcess u v N : ℝ))
    ((doublingWrapCount p v h : ℝ) / (h : ℝ))
  · exact oddSupportTail_eq_residue_div_add_excess A p hv u hstate
  · exact tendsto_cesaroMean_normalizedDoublingResidue p hv hperiod

/-- Explicit named-limit form of `ρ = w/h + lim mean(excess)`. -/
theorem reciprocalMass_eq_wrapRatio_add_oddTailExcessMean
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u) (excessMean : ℝ)
    (hexcess : Tendsto
      (cesaroMean (fun N : ℕ => (oddTailExcess u v N : ℝ)))
      atTop (nhds excessMean)) :
    reciprocalMass A =
      (doublingWrapCount p v h : ℝ) / (h : ℝ) + excessMean := by
  apply reciprocalMass_eq_residueMean_add_excessMean
    A hsum
    (fun N : ℕ => (doublingResidue p v N : ℝ) / (v : ℝ))
    (fun N : ℕ => (oddTailExcess u v N : ℝ))
    ((doublingWrapCount p v h : ℝ) / (h : ℝ)) excessMean
  · exact oddSupportTail_eq_residue_div_add_excess A p hv u hstate
  · exact tendsto_cesaroMean_normalizedDoublingResidue p hv hperiod
  · exact hexcess

/-- Fully instantiated wrap lower bound for a genuine odd support-tail
state. -/
theorem doublingWrapRatio_le_reciprocalMass
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u) :
    (doublingWrapCount p v h : ℝ) / (h : ℝ) ≤ reciprocalMass A := by
  apply wrapRatio_le_reciprocalMass_of_binaryCoeffTail_blocks
    A hsum h (doublingWrapCount p v h) hperiod.1
  intro q
  rw [← doublingWrapCount_mul_period p hperiod q]
  exact wrapCount_le_sum_supportTail_block
    A p hv hperiod u hstate (q * h)

theorem doublingWrapRatio_reciprocalMassDivergesOrAtLeast
    (A : Set ℕ) (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u) :
    ReciprocalMassDivergesOrAtLeast A
      ((doublingWrapCount p v h : ℝ) / (h : ℝ)) := by
  by_cases hsum : Summable (reciprocalSupportTerm A)
  · exact Or.inr
      (doublingWrapRatio_le_reciprocalMass A hsum p hv hperiod u hstate)
  · exact Or.inl hsum

/-- The positive-wrap corollary `1/h ≤ ρ(A)`, with divergence handled
honestly rather than relying on the nonsummable convention for `tsum`. -/
theorem one_div_period_reciprocalMassDivergesOrAtLeast
    (A : Set ℕ) (p : ℕ) {v h : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.Coprime v) (hperiod : IsDoublingPeriod v h)
    (u : ℕ → ℕ) (hstate : IsOddSupportTailState A p v u) :
    ReciprocalMassDivergesOrAtLeast A ((1 : ℝ) / (h : ℝ)) := by
  rcases doublingWrapRatio_reciprocalMassDivergesOrAtLeast
      A p (by omega) hperiod u hstate with hdiv | hbound
  · exact Or.inl hdiv
  · have hone : (1 : ℝ) / (h : ℝ) ≤
        (doublingWrapCount p v h : ℝ) / (h : ℝ) := by
      apply (div_le_div_iff_of_pos_right
        (by exact_mod_cast hperiod.1 : (0 : ℝ) < (h : ℝ))).2
      exact_mod_cast (doublingWrapCount_pos p hv hvodd hpv hperiod)
    exact Or.inr (hone.trans hbound)

/-! ## Fraction-facing global order-wrap theorem -/

theorem tendsto_shifted_binaryCoeffTail_supportCoeff_mean_reciprocalMass
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A)) (c : ℕ) :
    Tendsto
      (cesaroMean (fun N : ℕ =>
        binaryCoeffTail (supportCoeff A) (c + N)))
      atTop (nhds (reciprocalMass A)) := by
  let x : ℕ → ℝ := binaryCoeffTail (supportCoeff A)
  have hmean :
      Tendsto (fun N : ℕ => cesaroMean x (c + N)) atTop
        (nhds (reciprocalMass A)) := by
    exact
      (tendsto_binaryCoeffTail_supportCoeff_mean_reciprocalMass A hsum).comp
        (by simpa [add_comm] using tendsto_add_atTop_nat c)
  have hratio :
      Tendsto (fun N : ℕ => ((c + N : ℕ) : ℝ) / (N : ℝ)) atTop
        (nhds (1 : ℝ)) := by
    simpa using
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (c : ℝ) 0 1 (d := 1) one_ne_zero)
  have hprefix :
      Tendsto
        (fun N : ℕ => (∑ n ∈ Finset.range c, x n) / (N : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat
      (∑ n ∈ Finset.range c, x n)
  have hlim := (hmean.mul hratio).sub hprefix
  simpa only [mul_one, sub_zero] using hlim.congr'
    (Filter.Eventually.of_forall fun N => by
      rw [cesaroMean, cesaroMean]
      have hsplit := Finset.sum_range_add (f := x) c N
      have hcast : ((c + N : ℕ) : ℝ) = (c : ℝ) + (N : ℝ) := by norm_num
      rw [hcast]
      by_cases hN : (N : ℝ) = 0
      · simp [hN]
      · field_simp
        linarith)

theorem support_fraction_oddOrder_wrapRatio_le_reciprocalMass
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    (doublingWrapCount p.toNat v (oddDoublingOrder v hvodd) : ℝ) /
        (oddDoublingOrder v hvodd : ℝ) ≤ reciprocalMass A := by
  let h := oddDoublingOrder v hvodd
  have hperiod : IsDoublingPeriod v h :=
    oddDoublingOrder_isPeriod hv hvodd
  apply div_le_of_tendsto_cesaroMean_of_block_lower_bound
    (fun N : ℕ => binaryCoeffTail (supportCoeff A) (c + N))
    (reciprocalMass A) h
    (doublingWrapCount p.toNat v h) hperiod.1
  · exact
      tendsto_shifted_binaryCoeffTail_supportCoeff_mean_reciprocalMass
        A hsum c
  · intro q
    have hlocal := support_fraction_wrapCount_le_tail_block
      A hA p c (by omega : 0 < v) hvalue hperiod (q * h)
    rw [doublingWrapCount_mul_period p.toNat hperiod q] at hlocal
    simpa [Nat.add_assoc] using hlocal

theorem one_div_oddOrder_le_reciprocalMass_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.toNat.Coprime v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    (1 : ℝ) / (oddDoublingOrder v hvodd : ℝ) ≤ reciprocalMass A := by
  have hwrap :=
    support_fraction_oddOrder_wrapRatio_le_reciprocalMass
      A hA hsum p c hv hvodd hvalue
  have hw : (1 : ℝ) ≤
      (doublingWrapCount p.toNat v (oddDoublingOrder v hvodd) : ℝ) := by
    exact_mod_cast oddOrder_doublingWrapCount_pos p.toNat hv hvodd hpv
  calc
    (1 : ℝ) / (oddDoublingOrder v hvodd : ℝ) ≤
        (doublingWrapCount p.toNat v (oddDoublingOrder v hvodd) : ℝ) /
          (oddDoublingOrder v hvodd : ℝ) :=
      div_le_div_of_nonneg_right hw (by positivity)
    _ ≤ reciprocalMass A := hwrap

/-- Full finite-or-divergent formulation of the fraction-facing order-wrap
bound. -/
theorem support_fraction_oddOrder_wrapRatio_reciprocalMassDivergesOrAtLeast
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ReciprocalMassDivergesOrAtLeast A
      ((doublingWrapCount p.toNat v (oddDoublingOrder v hvodd) : ℝ) /
        (oddDoublingOrder v hvodd : ℝ)) := by
  by_cases hsum : Summable (reciprocalSupportTerm A)
  · exact Or.inr
      (support_fraction_oddOrder_wrapRatio_le_reciprocalMass
        A hA hsum p c hv hvodd hvalue)
  · exact Or.inl hsum

/-- For a reduced numerator modulo the odd part, rationality forces the
development's `1/ord_v(2)` reciprocal-mass lower bound. -/
theorem support_fraction_one_div_oddOrder_reciprocalMassDivergesOrAtLeast
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c : ℕ) {v : ℕ} (hv : 1 < v) (hvodd : Odd v)
    (hpv : p.toNat.Coprime v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ReciprocalMassDivergesOrAtLeast A
      ((1 : ℝ) / (oddDoublingOrder v hvodd : ℝ)) := by
  by_cases hsum : Summable (reciprocalSupportTerm A)
  · exact Or.inr
      (one_div_oddOrder_le_reciprocalMass_of_support_fraction
        A hA hsum p c hv hvodd hpv hvalue)
  · exact Or.inl hsum

/-! ## Shifted exact excess-mean identity -/

theorem tendsto_shifted_tail_excess_mean
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (c p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (htail : ∀ N : ℕ, (u N : ℝ) =
      (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + N))
    (hmod : ∀ N : ℕ, u N ≡ p * 2 ^ N [MOD v]) :
    Tendsto
      (cesaroMean (fun N : ℕ => ((u N / v : ℕ) : ℝ)))
      atTop
      (nhds (reciprocalMass A -
        (doublingWrapCount p v h : ℝ) / (h : ℝ))) := by
  have hdecomp : ∀ N : ℕ,
      binaryCoeffTail (supportCoeff A) (c + N) =
        (doublingResidue p v N : ℝ) / (v : ℝ) +
          ((u N / v : ℕ) : ℝ) := by
    intro N
    have hres : u N % v = doublingResidue p v N := by
      simpa [Nat.ModEq, doublingResidue] using hmod N
    have hnat :
        u N = v * (u N / v) + doublingResidue p v N := by
      rw [← hres]
      exact (Nat.div_add_mod (u N) v).symm
    have hreal := congrArg (fun n : ℕ => (n : ℝ)) hnat
    change (u N : ℝ) =
      (v * (u N / v) + doublingResidue p v N : ℕ) at hreal
    rw [htail N] at hreal
    push_cast at hreal
    have hvR : (v : ℝ) ≠ 0 := by positivity
    field_simp
    nlinarith
  have htailMean :=
    tendsto_shifted_binaryCoeffTail_supportCoeff_mean_reciprocalMass
      A hsum c
  have hresidueMean :=
    tendsto_cesaroMean_normalizedDoublingResidue p hv hperiod
  have hlim := htailMean.sub hresidueMean
  simpa only using hlim.congr'
    (Filter.Eventually.of_forall fun N => by
      simp only [cesaroMean, ← sub_div, ← Finset.sum_sub_distrib]
      refine congrArg (fun x : ℝ => x / (N : ℝ)) ?_
      refine Finset.sum_congr rfl fun n _ => ?_
      linarith [hdecomp n])

theorem exists_shifted_oddTailExcess_mean_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {v h : ℕ} (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (hperiod : IsDoublingPeriod v h) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      Tendsto
        (cesaroMean (fun n : ℕ => ((u n / v : ℕ) : ℝ)))
        atTop
        (nhds (reciprocalMass A -
          (doublingWrapCount p.toNat v h : ℝ) / (h : ℝ))) := by
  obtain ⟨u, htail, hpos, hrec, hmod⟩ :=
    exists_shifted_odd_tail_nat_states_of_support_fraction
      A hA p c v hv hvalue
  refine ⟨u, htail, hpos, hrec, hmod, ?_⟩
  exact tendsto_shifted_tail_excess_mean
    A hsum c p.toNat hv hperiod u htail hmod

/-! ## Boolean-collision lower bounds -/

/-- The natural-number realization of `ceil ((m - 1) / 2)` for positive
cardinalities.  For `m > 0`, this is exactly `m / 2`. -/
def booleanCollisionSurplus (m : ℕ) : ℕ := m / 2

theorem booleanCollisionSurplus_eq_ceil_sub_one_half
    {m : ℕ} (hm : 0 < m) :
    booleanCollisionSurplus m = (m - 1 + 1) / 2 := by
  simp [booleanCollisionSurplus, Nat.sub_add_cancel hm]

/-- Every marked support divisor of `n` contributes a distinct unit to
`supportCoeff A n`. -/
theorem card_le_supportCoeff_of_forced_divisors
    (A : Set ℕ) (F : Finset ℕ) (n : ℕ) (hn : n ≠ 0)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ n) :
    F.card ≤ supportCoeff A n := by
  classical
  rw [supportCoeff_eq_card_filter]
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hFdvd a ha, hn⟩, hFA a ha⟩

/-- Pure carry arithmetic behind the Boolean collision gain. -/
theorem booleanCollisionSurplus_le_of_carry
    (m f epsilon kPrev kNext : ℕ)
    (hmf : m ≤ f) (hepsilon : epsilon ≤ 1)
    (hcarry : f + kNext = epsilon + 2 * kPrev) :
    booleanCollisionSurplus m ≤ kPrev := by
  unfold booleanCollisionSurplus
  omega

/-- Support-specialized form of the same carry arithmetic. -/
theorem booleanCollisionSurplus_le_of_supportCoeff_carry
    (A : Set ℕ) (F : Finset ℕ) (n : ℕ) (hn : n ≠ 0)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ n)
    (epsilon kPrev kNext : ℕ) (hepsilon : epsilon ≤ 1)
    (hcarry : supportCoeff A n + kNext = epsilon + 2 * kPrev) :
    booleanCollisionSurplus F.card ≤ kPrev := by
  apply booleanCollisionSurplus_le_of_carry
    F.card (supportCoeff A n) epsilon kPrev kNext
  · exact card_le_supportCoeff_of_forced_divisors A F n hn hFA hFdvd
  · exact hepsilon
  · exact hcarry

/-- The quotient excess of a genuine odd tail state satisfies the exact
Boolean carry equation. -/
theorem supportCoeff_add_oddTailExcess_succ_eq_wrap_add_two_excess
    (A : Set ℕ) (p : ℕ) {v : ℕ} (hv : 0 < v) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u) (N : ℕ) :
    supportCoeff A (N + 1) + oddTailExcess u v (N + 1) =
      doublingWrapDigit p v N + 2 * oddTailExcess u v N := by
  have huRecR :
      (u (N + 1) : ℝ) +
          (v : ℝ) * (supportCoeff A (N + 1) : ℝ) =
        2 * (u N : ℝ) := by
    rw [hstate.1 (N + 1), hstate.1 N,
      binaryCoeffTail_succ
        (supportCoeff A) (supportCoeff_le_self A) N]
    ring
  have huRec :
      u (N + 1) + v * supportCoeff A (N + 1) = 2 * u N := by
    exact_mod_cast huRecR
  have hdecomp : ∀ j : ℕ,
      u j = v * oddTailExcess u v j + doublingResidue p v j := by
    intro j
    rw [oddTailExcess, ← hstate.2 j]
    exact (Nat.div_add_mod (u j) v).symm
  have hresidue := doublingResidue_carry p v N
  have hmulPlus :
      v * (supportCoeff A (N + 1) + oddTailExcess u v (N + 1)) +
          doublingResidue p v (N + 1) =
        v * (doublingWrapDigit p v N + 2 * oddTailExcess u v N) +
          doublingResidue p v (N + 1) := by
    calc
      v * (supportCoeff A (N + 1) + oddTailExcess u v (N + 1)) +
            doublingResidue p v (N + 1) =
          u (N + 1) + v * supportCoeff A (N + 1) := by
            rw [hdecomp (N + 1)]
            ring
      _ = 2 * u N := huRec
      _ = 2 * (v * oddTailExcess u v N +
            doublingResidue p v N) := by rw [hdecomp N]
      _ = v * (2 * oddTailExcess u v N) +
            2 * doublingResidue p v N := by ring
      _ = v * (2 * oddTailExcess u v N) +
            (v * doublingWrapDigit p v N +
              doublingResidue p v (N + 1)) := by rw [hresidue]
      _ = v * (doublingWrapDigit p v N +
            2 * oddTailExcess u v N) +
            doublingResidue p v (N + 1) := by ring
  have hmul :
      v * (supportCoeff A (N + 1) + oddTailExcess u v (N + 1)) =
        v * (doublingWrapDigit p v N + 2 * oddTailExcess u v N) :=
    Nat.add_right_cancel hmulPlus
  exact Nat.eq_of_mul_eq_mul_left hv hmul

/-- At every common multiple of a finite support subset, the preceding
odd-tail excess is at least its Boolean collision surplus. -/
theorem booleanCollisionSurplus_le_oddTailExcess
    (A : Set ℕ) (F : Finset ℕ) (p : ℕ) {v : ℕ} (hv : 0 < v)
    (u : ℕ → ℕ) (hstate : IsOddSupportTailState A p v u)
    {n : ℕ} (hn : 0 < n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ n) :
    booleanCollisionSurplus F.card ≤ oddTailExcess u v (n - 1) := by
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  apply booleanCollisionSurplus_le_of_supportCoeff_carry
    A F n hn.ne' hFA hFdvd
    (doublingWrapDigit p v (n - 1))
    (oddTailExcess u v (n - 1)) (oddTailExcess u v n)
  · exact doublingWrapDigit_le_one p hv (n - 1)
  · simpa [hnEq] using
      supportCoeff_add_oddTailExcess_succ_eq_wrap_add_two_excess
        A p hv u hstate (n - 1)

/-- A periodic arithmetic progression of excess spikes contributes at
least `q / L` to every Cesaro limit.  The residue `r` handles a finite
denominator shift. -/
theorem periodic_spike_div_le_of_tendsto_cesaroMean
    (k : ℕ → ℕ) (limit : ℝ) (L q r : ℕ)
    (hL : 0 < L) (hr : r < L)
    (hspike : ∀ j : ℕ, q ≤ k (r + j * L))
    (hlimit : Tendsto
      (cesaroMean (fun n : ℕ => (k n : ℝ))) atTop (nhds limit)) :
    (q : ℝ) / (L : ℝ) ≤ limit := by
  have hfinite : ∀ K : ℕ,
      K * q ≤ ∑ n ∈ Finset.range (K * L), k n := by
    intro K
    let S : Finset ℕ :=
      (Finset.range K).image (fun j : ℕ => r + j * L)
    have hinj : Function.Injective (fun j : ℕ => r + j * L) := by
      intro i j hij
      have hmul : i * L = j * L := Nat.add_left_cancel hij
      exact Nat.eq_of_mul_eq_mul_right hL hmul
    have hcard : S.card = K := by
      simp [S, Finset.card_image_iff.mpr hinj.injOn]
    have hSsub : S ⊆ Finset.range (K * L) := by
      intro n hn
      rcases Finset.mem_image.mp hn with ⟨j, hjK, rfl⟩
      have hjlt : j < K := Finset.mem_range.mp hjK
      exact Finset.mem_range.mpr (by nlinarith)
    calc
      K * q = ∑ _n ∈ S, q := by simp [hcard]
      _ ≤ ∑ n ∈ S, k n := by
        apply Finset.sum_le_sum
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨j, _, rfl⟩
        exact hspike j
      _ ≤ ∑ n ∈ Finset.range (K * L), k n := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hSsub
          (fun _ _ _ => Nat.zero_le _)
  have hmean : ∀ K : ℕ, 0 < K →
      (q : ℝ) / (L : ℝ) ≤
        cesaroMean (fun n : ℕ => (k n : ℝ)) (K * L) := by
    intro K hK
    rw [cesaroMean, le_div_iff₀ (by positivity : (0 : ℝ) < (K * L : ℕ))]
    have hfiniteR :
        ((K * q : ℕ) : ℝ) ≤
          ((∑ n ∈ Finset.range (K * L), k n : ℕ) : ℝ) := by
      exact_mod_cast hfinite K
    push_cast at hfiniteR
    calc
      (q : ℝ) / (L : ℝ) * (↑(K * L) : ℝ) = (K : ℝ) * (q : ℝ) := by
        push_cast
        field_simp
      _ ≤ ∑ n ∈ Finset.range (K * L), (k n : ℝ) := by
        simpa only [Nat.cast_sum] using hfiniteR
  have hmulTop : Tendsto (fun K : ℕ => K * L) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    exact (eventually_ge_atTop b).mono fun K hKb =>
      hKb.trans (Nat.le_mul_of_pos_right K hL)
  exact ge_of_tendsto (hlimit.comp hmulTop)
    ((eventually_gt_atTop (0 : ℕ)).mono fun K hK => hmean K hK)

/-- Removing or adding a fixed finite prefix does not change a Cesaro
limit. -/
theorem tendsto_cesaroMean_shift
    (x : ℕ → ℝ) (limit : ℝ) (c : ℕ)
    (hlimit : Tendsto (cesaroMean x) atTop (nhds limit)) :
    Tendsto (cesaroMean (fun n : ℕ => x (c + n))) atTop (nhds limit) := by
  have hshift :
      Tendsto (fun N : ℕ => cesaroMean x (c + N)) atTop (nhds limit) := by
    simpa [add_comm] using hlimit.comp (tendsto_add_atTop_nat c)
  have hratio :
      Tendsto (fun N : ℕ => ((c + N : ℕ) : ℝ) / (N : ℝ))
        atTop (nhds 1) := by
    have hcinv :
        Tendsto (fun N : ℕ => (c : ℝ) * (N : ℝ)⁻¹)
          atTop (nhds 0) :=
      by simpa only [mul_zero] using
        tendsto_inv_atTop_nhds_zero_nat.const_mul (c : ℝ)
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have htmp := hone.add hcinv
    simpa only [add_zero] using htmp.congr'
      ((eventually_gt_atTop (0 : ℕ)).mono fun N hN => by
        have hN0 : (N : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
        ring)
  let pref : ℝ := ∑ n ∈ Finset.range c, x n
  have hprefix :
      Tendsto (fun N : ℕ => pref / (N : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_inv_atTop_nhds_zero_nat.const_mul pref
  have hmain := (hshift.mul hratio).sub hprefix
  simpa only [mul_one, sub_zero] using hmain.congr'
    ((eventually_gt_atTop (0 : ℕ)).mono fun N hN => by
      rw [cesaroMean, cesaroMean]
      have hsum := Finset.sum_range_add (f := x) c N
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      have hcN0 : ((c + N : ℕ) : ℝ) ≠ 0 := by positivity
      dsimp [pref]
      rw [hsum]
      field_simp
      ring)

/-- Offset-free version of the progression-density lemma.  A fixed
preperiod does not affect the density `1/L`. -/
theorem periodic_spike_div_le_of_tendsto_cesaroMean_offset
    (k : ℕ → ℕ) (limit : ℝ) (L q r : ℕ)
    (hL : 0 < L) (hspike : ∀ j : ℕ, q ≤ k (r + j * L))
    (hlimit : Tendsto
      (cesaroMean (fun n : ℕ => (k n : ℝ))) atTop (nhds limit)) :
    (q : ℝ) / (L : ℝ) ≤ limit := by
  have hshift := tendsto_cesaroMean_shift
    (fun n : ℕ => (k n : ℝ)) limit r hlimit
  apply periodic_spike_div_le_of_tendsto_cesaroMean
    (fun n : ℕ => k (r + n)) limit L q 0 hL hL
  · intro j
    simpa [add_assoc] using hspike j
  · exact hshift

/-! ### Shifted odd-denominator states (the `2^c v` normalization) -/

/-- Odd tail state after removing the power-of-two part of a displayed
denominator. -/
def IsShiftedOddSupportTailState
    (A : Set ℕ) (p v c : ℕ) (u : ℕ → ℕ) : Prop :=
  (∀ N : ℕ,
      (u N : ℝ) = (v : ℝ) *
        binaryCoeffTail (supportCoeff A) (c + N)) ∧
    (∀ N : ℕ, u N % v = doublingResidue p v N)

theorem shiftedOddSupportTail_eq_residue_div_add_excess
    (A : Set ℕ) (p c : ℕ) {v : ℕ} (hv : 0 < v) (u : ℕ → ℕ)
    (hstate : IsShiftedOddSupportTailState A p v c u) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) (c + N) =
      (doublingResidue p v N : ℝ) / (v : ℝ) +
        (oddTailExcess u v N : ℝ) := by
  have hdecomp :
      u N = v * oddTailExcess u v N + doublingResidue p v N := by
    rw [oddTailExcess, ← hstate.2 N]
    exact (Nat.div_add_mod (u N) v).symm
  have hdecompR :
      (u N : ℝ) =
        (v * oddTailExcess u v N + doublingResidue p v N : ℕ) := by
    exact_mod_cast hdecomp
  rw [hstate.1 N] at hdecompR
  push_cast at hdecompR
  have hvR : (v : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

theorem shiftedSupportCoeff_add_oddTailExcess_succ_eq_wrap_add_two_excess
    (A : Set ℕ) (p c : ℕ) {v : ℕ} (hv : 0 < v) (u : ℕ → ℕ)
    (hstate : IsShiftedOddSupportTailState A p v c u) (N : ℕ) :
    supportCoeff A (c + N + 1) + oddTailExcess u v (N + 1) =
      doublingWrapDigit p v N + 2 * oddTailExcess u v N := by
  have huRecR :
      (u (N + 1) : ℝ) +
          (v : ℝ) * (supportCoeff A (c + N + 1) : ℝ) =
        2 * (u N : ℝ) := by
    rw [hstate.1 (N + 1), hstate.1 N,
      show c + (N + 1) = (c + N) + 1 by omega,
      binaryCoeffTail_succ
        (supportCoeff A) (supportCoeff_le_self A) (c + N)]
    ring
  have huRec :
      u (N + 1) + v * supportCoeff A (c + N + 1) = 2 * u N := by
    exact_mod_cast huRecR
  have hdecomp : ∀ j : ℕ,
      u j = v * oddTailExcess u v j + doublingResidue p v j := by
    intro j
    rw [oddTailExcess, ← hstate.2 j]
    exact (Nat.div_add_mod (u j) v).symm
  have hresidue := doublingResidue_carry p v N
  have hmulPlus :
      v * (supportCoeff A (c + N + 1) +
            oddTailExcess u v (N + 1)) +
          doublingResidue p v (N + 1) =
        v * (doublingWrapDigit p v N + 2 * oddTailExcess u v N) +
          doublingResidue p v (N + 1) := by
    calc
      v * (supportCoeff A (c + N + 1) +
              oddTailExcess u v (N + 1)) +
            doublingResidue p v (N + 1) =
          u (N + 1) + v * supportCoeff A (c + N + 1) := by
            rw [hdecomp (N + 1)]
            ring
      _ = 2 * u N := huRec
      _ = 2 * (v * oddTailExcess u v N +
            doublingResidue p v N) := by rw [hdecomp N]
      _ = v * (2 * oddTailExcess u v N) +
            2 * doublingResidue p v N := by ring
      _ = v * (2 * oddTailExcess u v N) +
            (v * doublingWrapDigit p v N +
              doublingResidue p v (N + 1)) := by rw [hresidue]
      _ = v * (doublingWrapDigit p v N +
            2 * oddTailExcess u v N) +
            doublingResidue p v (N + 1) := by ring
  have hmul := Nat.add_right_cancel hmulPlus
  exact Nat.eq_of_mul_eq_mul_left hv hmul

theorem booleanCollisionSurplus_le_shiftedOddTailExcess
    (A : Set ℕ) (F : Finset ℕ) (p c : ℕ) {v : ℕ} (hv : 0 < v)
    (u : ℕ → ℕ) (hstate : IsShiftedOddSupportTailState A p v c u)
    {n : ℕ} (hcn : c < n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ n) :
    booleanCollisionSurplus F.card ≤ oddTailExcess u v (n - c - 1) := by
  have hindex : c + (n - c - 1) + 1 = n := by omega
  apply booleanCollisionSurplus_le_of_supportCoeff_carry
    A F n (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le c) hcn)) hFA hFdvd
    (doublingWrapDigit p v (n - c - 1))
    (oddTailExcess u v (n - c - 1))
    (oddTailExcess u v ((n - c - 1) + 1))
  · exact doublingWrapDigit_le_one p hv (n - c - 1)
  · simpa [hindex] using
      shiftedSupportCoeff_add_oddTailExcess_succ_eq_wrap_add_two_excess
        A p c hv u hstate (n - c - 1)

/-- Under summability, the Cesàro mean of the shifted odd-tail excess is
`reciprocalMass A` minus the average wrap frequency
`doublingWrapCount p v h / h`. -/
theorem tendsto_shiftedOddTailExcess_mean
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p c : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (hstate : IsShiftedOddSupportTailState A p v c u) :
    Tendsto
      (cesaroMean (fun N : ℕ => (oddTailExcess u v N : ℝ)))
      atTop
      (nhds (reciprocalMass A -
        (doublingWrapCount p v h : ℝ) / (h : ℝ))) := by
  have htail := tendsto_cesaroMean_shift
    (binaryCoeffTail (supportCoeff A)) (reciprocalMass A) c
    (tendsto_binaryCoeffTail_supportCoeff_mean_reciprocalMass A hsum)
  have hresidue :=
    tendsto_cesaroMean_normalizedDoublingResidue p hv hperiod
  have hdiff := htail.sub hresidue
  simpa only using hdiff.congr'
    (Filter.Eventually.of_forall fun N => by
      simp only [cesaroMean, ← sub_div, ← Finset.sum_sub_distrib]
      refine congrArg (fun x : ℝ => x / (N : ℝ)) ?_
      refine Finset.sum_congr rfl fun n _ => ?_
      linarith [shiftedOddSupportTail_eq_residue_div_add_excess
        A p c hv u hstate n])

/-- Suppose every marked support element divides `L`.  Boolean collisions
then force a fixed excess on one arithmetic progression, contributing
`booleanCollisionSurplus F.card / L` to the Cesàro mean above the periodic
wrap contribution. -/
theorem shiftedBooleanCollision_wrap_bound_of_common_multiple
    (A : Set ℕ) (F : Finset ℕ) (p c : ℕ)
    (hsum : Summable (reciprocalSupportTerm A))
    {v h L : ℕ} (hv : 0 < v) (hperiod : IsDoublingPeriod v h)
    (hL : 0 < L) (hFA : ∀ a ∈ F, a ∈ A)
    (hFL : ∀ a ∈ F, a ∣ L)
    (u : ℕ → ℕ) (hstate : IsShiftedOddSupportTailState A p v c u) :
    (doublingWrapCount p v h : ℝ) / (h : ℝ) +
        (booleanCollisionSurplus F.card : ℝ) / (L : ℝ) ≤
      reciprocalMass A := by
  have hexcess := tendsto_shiftedOddTailExcess_mean
    A hsum p c hv hperiod u hstate
  let r : ℕ := (c + 1) * L - c - 1
  have hspike : ∀ j : ℕ,
      booleanCollisionSurplus F.card ≤
        oddTailExcess u v (r + j * L) := by
    intro j
    let n : ℕ := (c + 1 + j) * L
    have hcn : c < n := by
      dsimp [n]
      nlinarith
    have hnIndex : n - c - 1 = r + j * L := by
      have hle : c + 1 ≤ (c + 1) * L := by nlinarith
      have hcancel :
          (c + 1) * L - c - 1 + (c + 1) = (c + 1) * L := by
        omega
      apply Nat.add_right_cancel (m := c + 1)
      calc
        n - c - 1 + (c + 1) = n := by omega
        _ = (c + 1 + j) * L := rfl
        _ = (c + 1) * L + j * L := by ring
        _ = ((c + 1) * L - c - 1 + (c + 1)) + j * L := by
          rw [hcancel]
        _ = (r + j * L) + (c + 1) := by
          dsimp [r]
          ring
    rw [← hnIndex]
    apply booleanCollisionSurplus_le_shiftedOddTailExcess
      A F p c hv u hstate hcn hFA
    intro a ha
    exact dvd_trans (hFL a ha) (dvd_mul_left L (c + 1 + j))
  have hq := periodic_spike_div_le_of_tendsto_cesaroMean_offset
    (oddTailExcess u v)
    (reciprocalMass A -
      (doublingWrapCount p v h : ℝ) / (h : ℝ))
    L (booleanCollisionSurplus F.card) r hL hspike hexcess
  linarith

/-- An abstract Cesàro bound: a lower bound `q` for the odd-tail excess on one
residue class modulo `L` contributes `q / L` above the periodic wrap ratio.
The odd-tail state and the spike family are assumptions here, not outputs. -/
theorem wrapRatio_add_collisionSurplus_div_le_reciprocalMass
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℕ) {v h : ℕ} (hv : 0 < v)
    (hperiod : IsDoublingPeriod v h) (u : ℕ → ℕ)
    (hstate : IsOddSupportTailState A p v u)
    (L q r : ℕ) (hL : 0 < L) (hr : r < L)
    (hspike : ∀ j : ℕ, q ≤ oddTailExcess u v (r + j * L)) :
    (doublingWrapCount p v h : ℝ) / (h : ℝ) +
        (q : ℝ) / (L : ℝ) ≤ reciprocalMass A := by
  have hexcess := tendsto_oddTailExcess_mean
    A hsum p hv hperiod u hstate
  have hq : (q : ℝ) / (L : ℝ) ≤
      reciprocalMass A -
        (doublingWrapCount p v h : ℝ) / (h : ℝ) :=
    periodic_spike_div_le_of_tendsto_cesaroMean
      (oddTailExcess u v)
      (reciprocalMass A -
        (doublingWrapCount p v h : ℝ) / (h : ℝ))
      L q r hL hr hspike hexcess
  linarith

/-- Unshifted common-multiple specialization.  If every element of `F`
divides `L`, the positive multiples of `L` realize the collision surplus and
force a gain of `booleanCollisionSurplus F.card / L` above the periodic wrap
ratio. -/
theorem booleanCollision_wrap_bound_of_common_multiple
    (A : Set ℕ) (F : Finset ℕ) (p : ℕ)
    (hsum : Summable (reciprocalSupportTerm A))
    {v h L : ℕ} (hv : 0 < v) (hperiod : IsDoublingPeriod v h)
    (hL : 0 < L) (hFA : ∀ a ∈ F, a ∈ A)
    (hFL : ∀ a ∈ F, a ∣ L)
    (u : ℕ → ℕ) (hstate : IsOddSupportTailState A p v u) :
    (doublingWrapCount p v h : ℝ) / (h : ℝ) +
        (booleanCollisionSurplus F.card : ℝ) / (L : ℝ) ≤
      reciprocalMass A := by
  apply wrapRatio_add_collisionSurplus_div_le_reciprocalMass
    A hsum p hv hperiod u hstate
    L (booleanCollisionSurplus F.card) (L - 1) hL
  · omega
  · intro j
    let n := (j + 1) * L
    have hn : 0 < n := by
      dsimp [n]
      positivity
    have hnIndex : n - 1 = L - 1 + j * L := by
      apply Nat.add_right_cancel (m := 1)
      calc
        n - 1 + 1 = n := Nat.sub_add_cancel hn
        _ = (j + 1) * L := rfl
        _ = L + j * L := by ring
        _ = (L - 1 + 1) + j * L := by rw [Nat.sub_add_cancel hL]
        _ = (L - 1 + j * L) + 1 := by ring
    rw [← hnIndex]
    apply booleanCollisionSurplus_le_oddTailExcess
      A F p hv u hstate hn hFA
    intro a ha
    exact dvd_trans (hFL a ha) (dvd_mul_left L (j + 1))

/-! ### Dyadic-rational values and reciprocal mass -/

/-- Abstract positive-integer Cesàro lemma.  A positive integer sequence with
a density-`1/L` family of values at least two has Cesàro limit strictly greater
than one.  This statement is independent of support-series arithmetic. -/
theorem one_lt_of_tendsto_cesaroMean_of_positive_two_spikes
    (k : ℕ → ℕ) (limit : ℝ) (L r : ℕ) (hL : 0 < L)
    (hpos : ∀ n : ℕ, 0 < k n)
    (hspike : ∀ j : ℕ, 2 ≤ k (r + j * L))
    (hlimit : Tendsto
      (cesaroMean (fun n : ℕ => (k n : ℝ))) atTop (nhds limit)) :
    1 < limit := by
  let excess : ℕ → ℕ := fun n ↦ k n - 1
  have hexcessLimit :
      Tendsto (cesaroMean (fun n : ℕ => (excess n : ℝ))) atTop
        (nhds (limit - 1)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hsub := hlimit.sub hone
    apply hsub.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    rw [cesaroMean, cesaroMean]
    have hcast : ∀ n : ℕ,
        (excess n : ℝ) = (k n : ℝ) - 1 := by
      intro n
      dsimp [excess]
      rw [Nat.cast_sub (Nat.succ_le_iff.mpr (hpos n))]
      norm_num
    rw [Finset.sum_congr rfl fun n _ ↦ hcast n,
      Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hNR : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have hspikeExcess : ∀ j : ℕ, 1 ≤ excess (r + j * L) := by
    intro j
    have hk := hspike j
    dsimp [excess]
    omega
  have hgain := periodic_spike_div_le_of_tendsto_cesaroMean_offset
    excess (limit - 1) L 1 r hL hspikeExcess hexcessLimit
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hinv : (0 : ℝ) < (1 : ℝ) / (L : ℝ) := div_pos one_pos hLR
  linarith

/-- If `A` contains two distinct positive elements, the reciprocal support
terms are summable, and `erdosSupportSeries 2 A = p / 2^c`, then
`reciprocalMass A > 1`. -/
theorem one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    1 < reciprocalMass A := by
  let L := Nat.lcm a b
  have hL : 0 < L := by
    exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero ha.ne' hb.ne')
  obtain ⟨u, htail, hpos, _hrec, hmod⟩ :=
    exists_shifted_odd_tail_nat_states_of_support_fraction
      A ⟨a, ha, haA⟩ p c 1 (by norm_num) (by simpa using hvalue)
  have hstate : IsShiftedOddSupportTailState A p.toNat 1 c u := by
    refine ⟨?_, ?_⟩
    · intro n
      simpa using htail n
    · intro n
      simpa [doublingResidue, Nat.ModEq] using hmod n
  have hperiod : IsDoublingPeriod 1 1 := by
    norm_num [IsDoublingPeriod, Nat.ModEq]
  have hmeanRaw := tendsto_shiftedOddTailExcess_mean
    A hsum p.toNat c (v := 1) (h := 1) (by norm_num) hperiod u hstate
  have hmean :
      Tendsto (cesaroMean (fun n : ℕ => (u n : ℝ))) atTop
        (nhds (reciprocalMass A)) := by
    simpa [oddTailExcess, doublingWrapCount, doublingWrapDigit,
      doublingResidue, Nat.mod_one] using hmeanRaw
  let r : ℕ := (c + 1) * L - c - 1
  have hspike : ∀ j : ℕ, 2 ≤ u (r + j * L) := by
    intro j
    let n : ℕ := (c + 1 + j) * L
    have hcn : c < n := by
      dsimp [n]
      nlinarith
    have hnIndex : n - c - 1 = r + j * L := by
      have hcancel :
          (c + 1) * L - c - 1 + (c + 1) = (c + 1) * L := by
        have : c + 1 ≤ (c + 1) * L := by nlinarith
        omega
      apply Nat.add_right_cancel (m := c + 1)
      calc
        n - c - 1 + (c + 1) = n := by omega
        _ = (c + 1 + j) * L := rfl
        _ = (c + 1) * L + j * L := by ring
        _ = ((c + 1) * L - c - 1 + (c + 1)) + j * L := by
          rw [hcancel]
        _ = (r + j * L) + (c + 1) := by
          dsimp [r]
          ring
    have hcoeff : 2 ≤ supportCoeff A n := by
      have hLn : L ∣ n := dvd_mul_left L (c + 1 + j)
      have haL : a ∣ L := Nat.dvd_lcm_left a b
      have hbL : b ∣ L := Nat.dvd_lcm_right a b
      have hcard := card_le_supportCoeff_of_forced_divisors
        A {a, b} n
          (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le c) hcn)) (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact haA
          · exact hbA) (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact dvd_trans haL hLn
          · exact dvd_trans hbL hLn)
      simpa [hab] using hcard
    have hcarry :=
      shiftedSupportCoeff_add_oddTailExcess_succ_eq_wrap_add_two_excess
        A p.toNat c (v := 1) (by norm_num) u hstate (n - c - 1)
    have hnext : 0 < u ((n - c - 1) + 1) := hpos _
    have hindex : c + (n - c - 1) + 1 = n := by omega
    simp [oddTailExcess, doublingWrapDigit, doublingResidue, hindex] at hcarry
    have hprev : 2 ≤ u (n - c - 1) := by omega
    simpa [hnIndex] using hprev
  exact one_lt_of_tendsto_cesaroMean_of_positive_two_spikes
    u (reciprocalMass A) L r hL hpos hspike hmean

/-- For infinite `A`, a dyadic-rational value of `erdosSupportSeries 2 A`
implies that either the reciprocal support terms are not summable or their
`tsum` is strictly greater than one.

This becomes a contradiction only after a separate argument proves both
summability and `reciprocalMass A ≤ 1`; neither conclusion is supplied here. -/
theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
  by_cases hsum : Summable (reciprocalSupportTerm A)
  · right
    obtain ⟨a, haA, haNot⟩ := hAinf.exists_notMem_finset {0}
    have ha : 0 < a := Nat.pos_of_ne_zero (by simpa using haNot)
    obtain ⟨b, hbA, hbNot⟩ := hAinf.exists_notMem_finset {0, a}
    have hb0 : b ≠ 0 := by
      intro h
      apply hbNot
      simp [h]
    have hba : b ≠ a := by
      intro h
      apply hbNot
      simp [h]
    exact one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem
      A hsum p c ha (Nat.pos_of_ne_zero hb0) hba.symm haA hbA hvalue
  · exact Or.inl hsum

/-! ## Unbounded tail states from common multiples -/

/-- A finite marked subset of the support contributes at least its cardinality
to the coefficient at a common multiple.  Positivity of the next tail state
contributes the additional one.  The shifted index is `L - c - 1`. -/
theorem one_add_mul_card_le_two_mul_shifted_state
    (A : Set ℕ) (F : Finset ℕ) (c v L : ℕ) (u : ℕ → ℕ)
    (hcL : c < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    1 + v * F.card ≤ 2 * u (L - c - 1) := by
  have hL0 : L ≠ 0 := by omega
  have hcard : F.card ≤ supportCoeff A L :=
    card_le_supportCoeff_of_forced_divisors A F L hL0 hFA hFdvd
  have hindex : c + (L - c - 1) + 1 = L := by omega
  have hstep := hrec (L - c - 1)
  rw [hindex] at hstep
  have hnext : 1 ≤ u ((L - c - 1) + 1) := by
    exact hpos _
  have hmul : v * F.card ≤ v * supportCoeff A L :=
    Nat.mul_le_mul_left v hcard
  omega

/-- Unshifted wrapper for a recurrence indexed directly by
`supportCoeff A (n + 1)`. -/
theorem one_add_mul_card_le_two_mul_state
    (A : Set ℕ) (F : Finset ℕ) (v L : ℕ) (u : ℕ → ℕ)
    (hL : 0 < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    1 + v * F.card ≤ 2 * u (L - 1) := by
  apply one_add_mul_card_le_two_mul_shifted_state
    A F 0 v L u hL hpos
  · intro n
    simpa using hrec n
  · exact hFA
  · exact hFdvd

/-- Natural-number ceiling form of the shifted common-multiple inequality. -/
theorem one_add_mul_card_ceil_half_le_shifted_state
    (A : Set ℕ) (F : Finset ℕ) (c v L : ℕ) (u : ℕ → ℕ)
    (hcL : c < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    (1 + v * F.card + 1) / 2 ≤ u (L - c - 1) := by
  have hraw := one_add_mul_card_le_two_mul_shifted_state
    A F c v L u hcL hpos hrec hFA hFdvd
  omega

/-- Real-valued half form of the shifted common-multiple inequality. -/
theorem one_add_mul_card_half_le_shifted_state
    (A : Set ℕ) (F : Finset ℕ) (c v L : ℕ) (u : ℕ → ℕ)
    (hcL : c < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    ((1 + v * F.card : ℕ) : ℝ) / 2 ≤
      (u (L - c - 1) : ℝ) := by
  have hraw := one_add_mul_card_le_two_mul_shifted_state
    A F c v L u hcL hpos hrec hFA hFdvd
  have hrawR : ((1 + v * F.card : ℕ) : ℝ) ≤
      2 * (u (L - c - 1) : ℝ) := by
    exact_mod_cast hraw
  linarith

/-- A rational support value produces a positive shifted integer tail state
that also satisfies the common-multiple lower bound. -/
theorem exists_shifted_odd_tail_nat_state_with_common_multiple_bound_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (F : Finset ℕ) (p : ℤ) (c v L : ℕ)
    (hv : 0 < v) (hcL : c < L)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      1 + v * F.card ≤ 2 * u (L - c - 1) := by
  obtain ⟨u, htail, hpos, hrec, hmod⟩ :=
    exists_shifted_odd_tail_nat_states_of_support_fraction
      A hA p c v hv hvalue
  refine ⟨u, htail, hpos, hrec, hmod, ?_⟩
  exact one_add_mul_card_le_two_mul_shifted_state
    A F c v L u hcL hpos hrec hFA hFdvd

/-- Every positive shifted recurrence over an infinite support is unbounded.
For a proposed bound `B`, select `2B + 1` positive support elements and use
their product, multiplied by `c + 1`, as a common multiple. -/
theorem shifted_state_unbounded_of_infinite_support
    (A : Set ℕ) (hAinf : A.Infinite) (c v : ℕ) (hv : 0 < v)
    (u : ℕ → ℕ) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n) :
    ∀ B : ℕ, ∃ n : ℕ, B < u n := by
  intro B
  have hAposInf : (A \ {0}).Infinite :=
    hAinf.diff (Set.finite_singleton 0)
  obtain ⟨t, htA, htfinite, htcard⟩ :=
    hAposInf.exists_subset_ncard_eq (2 * B + 1)
  let F : Finset ℕ := htfinite.toFinset
  have hFcard : F.card = 2 * B + 1 := by
    dsimp [F]
    rw [← Set.ncard_eq_toFinset_card t htfinite]
    exact htcard
  have hFA : ∀ a ∈ F, a ∈ A := by
    intro a ha
    have hat : a ∈ t := by
      exact htfinite.mem_toFinset.mp (by simpa [F] using ha)
    exact (htA hat).1
  have hFpos : ∀ a ∈ F, 0 < a := by
    intro a ha
    have hat : a ∈ t := by
      exact htfinite.mem_toFinset.mp (by simpa [F] using ha)
    have ha0 : a ≠ 0 := by
      simpa using (htA hat).2
    exact Nat.pos_of_ne_zero ha0
  let P : ℕ := ∏ a ∈ F, a
  have hP : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun a ha ↦ hFpos a ha
  let L : ℕ := (c + 1) * P
  have hcL : c < L := by
    have hPone : 1 ≤ P := hP
    dsimp [L]
    nlinarith
  have hFdvd : ∀ a ∈ F, a ∣ L := by
    intro a ha
    have haP : a ∣ P := by
      dsimp [P]
      exact Finset.dvd_prod_of_mem (fun x : ℕ ↦ x) ha
    exact dvd_trans haP (by
      dsimp [L]
      exact dvd_mul_left P (c + 1))
  have hbound := one_add_mul_card_le_two_mul_shifted_state
    A F c v L u hcL hpos hrec hFA hFdvd
  rw [hFcard] at hbound
  have hvone : 1 ≤ v := hv
  have hvmul : 2 * B + 1 ≤ v * (2 * B + 1) := by
    simpa using Nat.mul_le_mul_right (2 * B + 1) hvone
  refine ⟨L - c - 1, ?_⟩
  omega

/-- If an infinite support has the displayed rational value, its positive
shifted integer tail state is unbounded. -/
theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n) := by
  obtain ⟨a, haA, ha0⟩ := hAinf.exists_notMem_finset {0}
  have ha : 0 < a := Nat.pos_of_ne_zero (by simpa using ha0)
  obtain ⟨u, htail, hpos, hrec, hmod⟩ :=
    exists_shifted_odd_tail_nat_states_of_support_fraction
      A ⟨a, ha, haA⟩ p c v hv hvalue
  refine ⟨u, htail, hpos, hrec, hmod, ?_⟩
  exact shifted_state_unbounded_of_infinite_support
    A hAinf c v hv u hpos hrec

/-- In the finite `{2, 3}` example, each of the first 66 tested common
multiples gives the same preceding carry value `26`; the checked indices are
`6 * (k + 1) - 1` for `0 ≤ k < 66`. -/
theorem carryOrbit23_common_multiple_bound_validation66 :
    ∀ k ∈ Finset.range 66,
      (1 : ℤ) + 21 * ({2, 3} : Finset ℕ).card ≤
        2 * carryOrbit23 (6 * k + 5) := by
  intro k _hk
  have hmod : (6 * k + 5) % 6 = 5 := by omega
  simp [carryOrbit23, hmod]

/-! ## Lean-checked finite validation -/

/-- Reduced numerator starts modulo `v`, represented as a computable list for
the native finite certificate. -/
def coprimeResidueStarts (v : ℕ) : List ℕ :=
  (List.range v).filter fun p ↦ p.Coprime v

/-- Does the starting residue lie in the displayed power-of-two orbit? -/
def isPowerOfTwoOrbitStart (p v h : ℕ) : Bool :=
  (List.range h).any fun a ↦ doublingResidue p v 0 == 2 ^ a

/-- Computable validation of positivity and both directions of the one-wrap
classification on one finite modulus/order row.  This is validation evidence,
not the source of the universal theorem above. -/
def orderWrapValidationRow (v h : ℕ) : Bool :=
  decide (0 < h) && decide (2 ^ h % v = 1) &&
    (coprimeResidueStarts v).all fun p ↦
      decide (0 < doublingWrapCount p v h) &&
        (decide (doublingWrapCount p v h = 1) ==
          (decide (v = 2 ^ h - 1) && isPowerOfTwoOrbitStart p v h))

/-- The twelve modulus/order rows in the 446-orbit validation. -/
def orderWrapValidationRows : List (ℕ × ℕ) :=
  [(3, 2), (5, 4), (7, 3), (9, 6), (11, 10), (13, 12),
    (15, 4), (21, 6), (31, 5), (33, 10), (63, 6), (341, 10)]

def orderWrapValidatedStartCount : ℕ :=
  orderWrapValidationRows.foldl
    (fun total row ↦ total + (coprimeResidueStarts row.1).length) 0

def orderWrapValidation446 : Bool :=
  orderWrapValidationRows.all fun row ↦ orderWrapValidationRow row.1 row.2

/-- Exact minimum-wrap certificate on a single finite row. -/
def wrapMinimumCertificate (v h minimum : ℕ) : Bool :=
  ((coprimeResidueStarts v).all fun p ↦
      decide (minimum ≤ doublingWrapCount p v h)) &&
    ((coprimeResidueStarts v).any fun p ↦
      decide (doublingWrapCount p v h = minimum))

set_option maxRecDepth 100000 in
theorem orderWrapValidatedStartCount_eq_446 :
    orderWrapValidatedStartCount = 446 := by decide

set_option maxRecDepth 100000 in
theorem orderWrapValidation446_passes :
    orderWrapValidation446 = true := by decide

set_option maxRecDepth 100000 in
/-- The checked minimum wrap ratios are respectively
`1/2`, `2/4`, `1/3`, `1/4`, and `1/5`. -/
theorem orderWrap_minima_table_passes :
    wrapMinimumCertificate 3 2 1 = true ∧
    wrapMinimumCertificate 5 4 2 = true ∧
    wrapMinimumCertificate 7 3 1 = true ∧
    wrapMinimumCertificate 15 4 1 = true ∧
    wrapMinimumCertificate 31 5 1 = true := by
  decide

end Erdos257PeriodNoncollapse
