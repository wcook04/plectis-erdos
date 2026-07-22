import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the three-prime running-LCM coordinate

This module starts the problem-owned formalization of the first unresolved
three-prime case. It records the exact computational height used by the
running-LCM representation, its cubic majorant, the smallest non-separation
fixture for `{2,3,5}`, the variable-base tail-state update, and the uniform
quadratic bound for actual filtered smooth-number shells.

No declaration here asserts irrationality or transcendence of a three-prime
value. The missing producer is still an infinite residue-escape or genuinely
higher-dimensional analytic theorem.
-/

namespace ErdosProblems.Erdos269

/-- The `{p,q,r}`-smooth lattice point with exponent vector `(i,j,k)`. -/
def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

/-- The product of the largest pure `p`-, `q`-, and `r`-powers not exceeding
`x`. For a `{p,q,r}`-smooth `x`, this is the running LCM of the smooth prefix. -/
def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

/-- The exact rational lattice kernel attached to the running-LCM height. -/
def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

/-- Exponent vectors of the actual `{p,q,r}`-smooth prefix up to `x`.  The
logarithmic box makes the prefix finite; the final filter keeps only products
which really lie below `x`. -/
def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

/-- The literal running LCM of the finite smooth prefix. -/
def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2

/-- Every actual smooth prefix value divides the coordinatewise maximal
pure-power product. -/
theorem smooth3Val_dvd_threePrimeHeight_of_mem
    {p q r x : ℕ} {e : ℕ × ℕ × ℕ}
    (he : e ∈ smoothPrefixExponents p q r x) :
    smooth3Val p q r e.1 e.2.1 e.2.2 ∣ threePrimeHeight p q r x := by
  have hbox := (Finset.mem_filter.mp he).1
  have hpBox := Finset.mem_product.mp hbox
  have hqrBox := Finset.mem_product.mp hpBox.2
  have hpExp : e.1 ≤ Nat.log p x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hpBox.1)
  have hqExp : e.2.1 ≤ Nat.log q x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqrBox.1)
  have hrExp : e.2.2 ≤ Nat.log r x := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hqrBox.2)
  exact mul_dvd_mul
    (mul_dvd_mul (pow_dvd_pow p hpExp) (pow_dvd_pow q hqExp))
    (pow_dvd_pow r hrExp)

/-- The literal smooth-prefix LCM divides the computational height. -/
theorem smoothPrefixLcm_dvd_threePrimeHeight (p q r x : ℕ) :
    smoothPrefixLcm p q r x ∣ threePrimeHeight p q r x := by
  apply Finset.lcm_dvd
  intro e he
  exact smooth3Val_dvd_threePrimeHeight_of_mem he

/-- The pure `p` height component occurs in the actual prefix. -/
theorem pureFirst_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (Nat.log p x, 0, 0) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
        Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self p hx

/-- The pure `q` height component occurs in the actual prefix. -/
theorem pureSecond_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (0, Nat.log q x, 0) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_self _),
        Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self q hx

/-- The pure `r` height component occurs in the actual prefix. -/
theorem pureThird_mem_smoothPrefixExponents
    {p q r x : ℕ} (hx : x ≠ 0) :
    (0, 0, Nat.log r x) ∈ smoothPrefixExponents p q r x := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.zero_lt_succ _),
        Finset.mem_range.mpr (Nat.lt_succ_self _)⟩
  · simpa [smooth3Val] using Nat.pow_log_le_self r hx

/-- Exact running-LCM identity for three pairwise-distinct primes. -/
theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x := by
  apply Nat.dvd_antisymm (smoothPrefixLcm_dvd_threePrimeHeight p q r x)
  have hpDvd : p ^ Nat.log p x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureFirst_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hqDvd : q ^ Nat.log q x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureSecond_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hrDvd : r ^ Nat.log r x ∣ smoothPrefixLcm p q r x := by
    simpa [smoothPrefixLcm, smooth3Val] using
      (Finset.dvd_lcm
        (f := fun e : ℕ × ℕ × ℕ => smooth3Val p q r e.1 e.2.1 e.2.2)
        (pureThird_mem_smoothPrefixExponents (p := p) (q := q) (r := r) hx))
  have hpqCoprime :
      (p ^ Nat.log p x).Coprime (q ^ Nat.log q x) :=
    Nat.coprime_pow_primes _ _ hp hq hpq
  have hprCoprime :
      (p ^ Nat.log p x).Coprime (r ^ Nat.log r x) :=
    Nat.coprime_pow_primes _ _ hp hr hpr
  have hqrCoprime :
      (q ^ Nat.log q x).Coprime (r ^ Nat.log r x) :=
    Nat.coprime_pow_primes _ _ hq hr hqr
  have hpqDvd :
      p ^ Nat.log p x * q ^ Nat.log q x ∣ smoothPrefixLcm p q r x :=
    hpqCoprime.mul_dvd_of_dvd_of_dvd hpDvd hqDvd
  have hpqrCoprime :
      (p ^ Nat.log p x * q ^ Nat.log q x).Coprime
        (r ^ Nat.log r x) :=
    Nat.coprime_mul_iff_left.mpr ⟨hprCoprime, hqrCoprime⟩
  exact hpqrCoprime.mul_dvd_of_dvd_of_dvd hpqDvd hrDvd

/-- Two cutoffs lie in the same three-prime logarithmic cell when none of the
three maximal pure-power coordinates changes between them. -/
def SameThreePrimeLogCell (p q r x y : ℕ) : Prop :=
  Nat.log p x = Nat.log p y ∧
    Nat.log q x = Nat.log q y ∧
      Nat.log r x = Nat.log r y

/-- The computational height is exactly constant on every logarithmic cell. -/
theorem threePrimeHeight_eq_of_sameLogCell
    {p q r x y : ℕ} (hcell : SameThreePrimeLogCell p q r x y) :
    threePrimeHeight p q r x = threePrimeHeight p q r y := by
  rcases hcell with ⟨hp, hq, hr⟩
  simp [threePrimeHeight, hp, hq, hr]

/-- For pairwise-distinct primes, the literal smooth-prefix LCM is constant on
every three-prime logarithmic cell.  This is the finite formal interface behind
the prime-power jump expansion: the LCM can change only when one logarithmic
coordinate changes. -/
theorem smoothPrefixLcm_eq_of_sameLogCell
    {p q r x y : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hcell : SameThreePrimeLogCell p q r x y) :
    smoothPrefixLcm p q r x = smoothPrefixLcm p q r y := by
  rw [smoothPrefixLcm_eq_threePrimeHeight hp hq hr hpq hpr hqr hx,
    smoothPrefixLcm_eq_threePrimeHeight hp hq hr hpq hpr hqr hy]
  exact threePrimeHeight_eq_of_sameLogCell hcell

/-- The rational lattice kernel is likewise constant whenever its two smooth
arguments occupy the same logarithmic cell. -/
theorem threePrimeKernelQ_eq_of_sameLogCell
    {p q r i j k i' j' k' : ℕ}
    (hcell : SameThreePrimeLogCell p q r
      (smooth3Val p q r i j k) (smooth3Val p q r i' j' k')) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k' := by
  simp only [threePrimeKernelQ]
  rw [threePrimeHeight_eq_of_sameLogCell hcell]

/-- Each pure-power component of the height is at most `x`, so the three-prime
height is bounded by `x³`. -/
theorem threePrimeHeight_le_cube
    (p q r x : ℕ) (hx : x ≠ 0) :
    threePrimeHeight p q r x ≤ x ^ 3 := by
  have hp := Nat.pow_log_le_self p hx
  have hq := Nat.pow_log_le_self q hx
  have hr := Nat.pow_log_le_self r hx
  calc
    threePrimeHeight p q r x
        ≤ (x * x) * x := Nat.mul_le_mul (Nat.mul_le_mul hp hq) hr
    _ = x ^ 3 := by ring

/-! The first exact `{2,3,5}` kernel values. -/

@[simp] theorem kernel_235_origin :
    threePrimeKernelQ 2 3 5 0 0 0 = 1 := by
  have h2 : Nat.log 2 1 = 0 := Nat.log_of_lt (by norm_num)
  have h3 : Nat.log 3 1 = 0 := Nat.log_of_lt (by norm_num)
  have h5 : Nat.log 5 1 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_two :
    threePrimeKernelQ 2 3 5 1 0 0 = 1 / 2 := by
  have h2 : Nat.log 2 2 = 1 := by
    simpa using Nat.log_pow (b := 2) (by norm_num : 1 < 2) 1
  have h3 : Nat.log 3 2 = 0 := Nat.log_of_lt (by norm_num)
  have h5 : Nat.log 5 2 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_three :
    threePrimeKernelQ 2 3 5 0 1 0 = 1 / 6 := by
  have h2 : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h3 : Nat.log 3 3 = 1 := by
    simpa using Nat.log_pow (b := 3) (by norm_num : 1 < 3) 1
  have h5 : Nat.log 5 3 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_six :
    threePrimeKernelQ 2 3 5 1 1 0 = 1 / 60 := by
  have h2 : Nat.log 2 6 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h3 : Nat.log 3 6 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h5 : Nat.log 5 6 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

/-- The smallest exact witness that the three-prime kernel is not rank one.
The two sides are `1/60` and `1/12`. -/
theorem kernel_235_not_rankOne :
    threePrimeKernelQ 2 3 5 0 0 0 *
        threePrimeKernelQ 2 3 5 1 1 0 ≠
      threePrimeKernelQ 2 3 5 1 0 0 *
        threePrimeKernelQ 2 3 5 0 1 0 := by
  norm_num

/-- One step of the exact variable-base tail orbit from the jump expansion. -/
def tailStateStep (base digit state : ℤ) : ℤ :=
  base * (state - digit)

theorem tailStateStep_eq (base digit state next : ℤ) :
    next = tailStateStep base digit state ↔
      next = base * state - base * digit := by
  simp [tailStateStep, mul_sub]

/-! ## Exact short-shell multiplicity bounds -/

/-- Exponent triples in a half-open multiplicative shell, with explicit
coordinate bounds.  The coordinate bounds are the interface to the pure-power
jump heights; the interval filter is the actual smooth-number shell. -/
def smoothExponentShell
    (p q r lo hi hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (hp + 1)).product
      ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))).filter
    fun e => lo ≤ smooth3Val p q r e.1 e.2.1 e.2.2 ∧
      smooth3Val p q r e.1 e.2.1 e.2.2 < hi

/-- In an interval of multiplicative width at most `base`, fixing the other
factors leaves at most one exponent of `base`. -/
theorem exponent_unique_in_short_interval
    {base lo hi weight a b : ℕ}
    (hbase : 0 < base) (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hpow : base ^ (a + 1) ≤ base ^ b :=
      Nat.pow_le_pow_right hbase (by omega)
    have hcontra : hi < hi := calc
      hi ≤ base * lo := hwidth
      _ ≤ base * (base ^ a * weight) := Nat.mul_le_mul_left base haLo
      _ = base ^ (a + 1) * weight := by
        rw [pow_succ]
        ac_rfl
      _ ≤ base ^ b * weight := Nat.mul_le_mul_right weight hpow
      _ < hi := hbHi
    exact (Nat.lt_irrefl hi hcontra).elim
  · exact hab
  · have hpow : base ^ (b + 1) ≤ base ^ a :=
      Nat.pow_le_pow_right hbase (by omega)
    have hcontra : hi < hi := calc
      hi ≤ base * lo := hwidth
      _ ≤ base * (base ^ b * weight) := Nat.mul_le_mul_left base hbLo
      _ = base ^ (b + 1) * weight := by
        rw [pow_succ]
        ac_rfl
      _ ≤ base ^ a * weight := Nat.mul_le_mul_right weight hpow
      _ < hi := haHi
    exact (Nat.lt_irrefl hi hcontra).elim

/-- Projecting away the first exponent is injective on a shell whose width is
at most the first base.  Consequently the shell has at most the size of the
other two exponent ranges. -/
theorem smoothExponentShell_card_le_dropFirst
    {p q r lo hi hp hq hr : ℕ}
    (hpPos : 0 < p) (hwidth : hi ≤ p * lo) :
    (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (hq + 1) * (hr + 1) := by
  classical
  let target := (Finset.range (hq + 1)).product (Finset.range (hr + 1))
  have hcard :
      (smoothExponentShell p q r lo hi hp hq hr).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn (fun e : ℕ × ℕ × ℕ => e.2) ?_ ?_
    · intro e he
      change e ∈ smoothExponentShell p q r lo hi hp hq hr at he
      change e.2 ∈ target
      rcases e with ⟨a, b, c⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he
      have houter := Finset.mem_product.mp he.1
      have hinner := Finset.mem_product.mp houter.2
      exact Finset.mem_product.mpr
        ⟨hinner.1, hinner.2⟩
    · intro e₁ he₁ e₂ he₂ hproj
      change e₁ ∈ smoothExponentShell p q r lo hi hp hq hr at he₁
      change e₂ ∈ smoothExponentShell p q r lo hi hp hq hr at he₂
      rcases e₁ with ⟨a₁, b₁, c₁⟩
      rcases e₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he₁ he₂
      have ha₁Lo : lo ≤ p ^ a₁ * (q ^ b₁ * r ^ c₁) := by
        simpa [smooth3Val, mul_assoc] using he₁.2.1
      have ha₁Hi : p ^ a₁ * (q ^ b₁ * r ^ c₁) < hi := by
        simpa [smooth3Val, mul_assoc] using he₁.2.2
      have ha₂Lo : lo ≤ p ^ a₂ * (q ^ b₁ * r ^ c₁) := by
        simpa [smooth3Val, mul_assoc] using he₂.2.1
      have ha₂Hi : p ^ a₂ * (q ^ b₁ * r ^ c₁) < hi := by
        simpa [smooth3Val, mul_assoc] using he₂.2.2
      have ha : a₁ = a₂ := exponent_unique_in_short_interval hpPos hwidth
        ha₁Lo ha₁Hi ha₂Lo ha₂Hi
      simp [ha]
  simpa [target] using hcard

/-- The symmetric projection needed when the third height is the largest:
fixing the first two exponents leaves at most one exponent of the third base. -/
theorem smoothExponentShell_card_le_dropThird
    {p q r lo hi hp hq hr : ℕ}
    (hrPos : 0 < r) (hwidth : hi ≤ r * lo) :
    (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (hp + 1) * (hq + 1) := by
  classical
  let target := (Finset.range (hp + 1)).product (Finset.range (hq + 1))
  have hcard :
      (smoothExponentShell p q r lo hi hp hq hr).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn
      (fun e : ℕ × ℕ × ℕ => (e.1, e.2.1)) ?_ ?_
    · intro e he
      change e ∈ smoothExponentShell p q r lo hi hp hq hr at he
      change (e.1, e.2.1) ∈ target
      rcases e with ⟨a, b, c⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he
      have houter := Finset.mem_product.mp he.1
      have hinner := Finset.mem_product.mp houter.2
      exact Finset.mem_product.mpr ⟨houter.1, hinner.1⟩
    · intro e₁ he₁ e₂ he₂ hproj
      change e₁ ∈ smoothExponentShell p q r lo hi hp hq hr at he₁
      change e₂ ∈ smoothExponentShell p q r lo hi hp hq hr at he₂
      rcases e₁ with ⟨a₁, b₁, c₁⟩
      rcases e₂ with ⟨a₂, b₂, c₂⟩
      simp only [Prod.mk.injEq] at hproj
      rcases hproj with ⟨rfl, rfl⟩
      simp only [smoothExponentShell, Finset.mem_filter] at he₁ he₂
      have hc₁Lo : lo ≤ r ^ c₁ * (p ^ a₁ * q ^ b₁) := by
        simpa [smooth3Val, mul_assoc, mul_comm, mul_left_comm] using he₁.2.1
      have hc₁Hi : r ^ c₁ * (p ^ a₁ * q ^ b₁) < hi := by
        simpa [smooth3Val, mul_assoc, mul_comm, mul_left_comm] using he₁.2.2
      have hc₂Lo : lo ≤ r ^ c₂ * (p ^ a₁ * q ^ b₁) := by
        simpa [smooth3Val, mul_assoc, mul_comm, mul_left_comm] using he₂.2.1
      have hc₂Hi : r ^ c₂ * (p ^ a₁ * q ^ b₁) < hi := by
        simpa [smooth3Val, mul_assoc, mul_comm, mul_left_comm] using he₂.2.2
      have hc : c₁ = c₂ := exponent_unique_in_short_interval hrPos hwidth
        hc₁Lo hc₁Hi hc₂Lo hc₂Hi
      simp [hc]
  simpa [target] using hcard

/-- If `a ≤ b ≤ c` and the three heights sum to `j`, then the product of
the two smaller shifted heights satisfies the clean quadratic estimate used
in the scaled-tail analysis.  This is the denominator-free form of
`(a+1)(b+1) ≤ (j+3)²/9`. -/
theorem sorted_pair_quadratic
    {a b c j : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hsum : a + b + c = j) :
    9 * ((a + 1) * (b + 1)) ≤ (j + 3) ^ 2 := by
  have hj : a + 2 * b ≤ j := by omega
  let d := b - a
  have hd : d + a = b := by
    dsimp [d]
    omega
  have hnon : 0 ≤ d * (3 * a + 4 * d + 3) := Nat.zero_le _
  have hlocal :
      9 * ((a + 1) * (b + 1)) ≤ (a + 2 * b + 3) ^ 2 := by
    nlinarith
  exact hlocal.trans (Nat.pow_le_pow_left (Nat.add_le_add_right hj 3) 2)

/-- The exact smooth shell inherits the uniform quadratic multiplicity bound
once its height coordinates are sorted and sum to the jump index. -/
theorem smoothExponentShell_card_quadratic
    {p q r lo hi hp hq hr j : ℕ}
    (hrPos : 0 < r) (hwidth : hi ≤ r * lo)
    (hpq : hp ≤ hq) (hqr : hq ≤ hr)
    (hsum : hp + hq + hr = j) :
    9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤
      (j + 3) ^ 2 := by
  exact (Nat.mul_le_mul_left 9
    (smoothExponentShell_card_le_dropThird hrPos hwidth)).trans
      (sorted_pair_quadratic hpq hqr hsum)

end ErdosProblems.Erdos269
