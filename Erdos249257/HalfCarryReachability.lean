import Erdos249257.BooleanMobiusCarry
import Erdos249257.DyadicPrefixCompression
import Erdos249257.MersenneLambertLadder
import Mathlib.Order.KonigLemma

/-!
# Finite reachability for the canonical half carry

This module isolates the finite-prefix and compactness side of the question
whether the binary Mersenne achievement set contains `1 / 2`.

The finite carry is

`K₁ = 1`, `Kₙ = 2 Kₙ₋₁ - ∑_{d ∣ n} a_d`,

with `a₁ = 0`.  We use the strip `1 ≤ Kₙ ≤ 2 * Nat.sqrt n + 4`.

The arithmetic theorem `evenSeamReachable_iff` proves the exact one-hole
description of an unresolved half-divisor bit.  It leaves only the arithmetic
question whether that hole can lie inside the strip after the depth-18 base.
No seam-escape assertion, infinite support, or decision of Erdős #257 is made
here.
-/

namespace Erdos249257.HalfCarryReachability

open Filter Set

/-! ## The finite carry and its strip -/

/-- The discrete square-root strip used by the half-carry search. -/
def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4

/-- The integer carry whose state at time `N` is the packet's `K_{N+1}`. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

@[simp] theorem integerHalfCarry_zero (A : Set ℕ) :
    integerHalfCarry A 0 = 1 := rfl

@[simp] theorem integerHalfCarry_succ (A : Set ℕ) (N : ℕ) :
    integerHalfCarry A (N + 1) =
      2 * integerHalfCarry A N - (supportCoeff A (N + 2) : ℤ) := by
  rfl

/-- Restricting a support above `M` does not change its integer half carry
through level `M`. -/
theorem integerHalfCarry_inter_Iic_eq_of_succ_le
    (A : Set ℕ) (M : ℕ) :
    ∀ N : ℕ, N + 1 ≤ M →
      integerHalfCarry (A ∩ Set.Iic M) N = integerHalfCarry A N := by
  intro N hNM
  induction N with
  | zero => simp
  | succ N ih =>
      rw [integerHalfCarry_succ, integerHalfCarry_succ,
        ih (by omega), supportCoeff_inter_Iic_eq_of_le A (by omega)]

/-- Inserting a support bit at row `n` does not change any carry whose next
coefficient row is still strictly before `n`.  This is the exact bridge used
to regard the two choices of the row-`n` bit as children of one parent. -/
theorem integerHalfCarry_insert_future_eq
    (A : Set ℕ) {m n : ℕ} (hmn : m + 2 ≤ n) :
    integerHalfCarry (insert n A) m = integerHalfCarry A m := by
  have hm : m + 1 ≤ n - 1 := by omega
  calc
    integerHalfCarry (insert n A) m =
        integerHalfCarry (insert n A ∩ Set.Iic (n - 1)) m :=
      (integerHalfCarry_inter_Iic_eq_of_succ_le (insert n A) (n - 1) m hm).symm
    _ = integerHalfCarry (A ∩ Set.Iic (n - 1)) m := by
      apply congrArg (fun S : Set ℕ => integerHalfCarry S m)
      ext d
      change ((d = n ∨ d ∈ A) ∧ d ≤ n - 1) ↔ d ∈ A ∧ d ≤ n - 1
      constructor
      · rintro ⟨rfl | hdA, hdle⟩
        · omega
        · exact ⟨hdA, hdle⟩
      · rintro ⟨hdA, hdle⟩
        exact ⟨Or.inr hdA, hdle⟩
    _ = integerHalfCarry A m :=
      integerHalfCarry_inter_Iic_eq_of_succ_le A (n - 1) m hm

/-- The elementary square-root change across one row. -/
theorem sqrt_le_pred_sqrt_add_one {n : ℕ} (hn : 1 ≤ n) :
    Nat.sqrt n ≤ Nat.sqrt (n - 1) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa using Nat.sqrt_succ_le_succ_sqrt m

/-- The sharp divisor envelope leaves enough room for the inverse parent at
the preceding row. -/
theorem halfStripBound_add_coeff_le_two_mul_pred
    {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ 2 * Nat.sqrt n) :
    halfStripBound n + c ≤ 2 * halfStripBound (n - 1) := by
  have hsqrt := sqrt_le_pred_sqrt_add_one (show 1 ≤ n by omega)
  unfold halfStripBound
  omega

/-! ## Finite Boolean words and restriction -/

/-- A Boolean support word through exponent `N`.  Index zero is retained so
restriction is literal; admissibility forces exponents zero and one off. -/
abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

/-- Restrict a word at level `N` to an earlier level `M`. -/
def restrictWord {M N : ℕ} (hMN : M ≤ N) (a : HalfWord N) : HalfWord M :=
  fun i ↦ a ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hMN)⟩

@[simp] theorem restrictWord_refl {N : ℕ} (a : HalfWord N) :
    restrictWord (le_refl N) a = a := by
  funext i
  rfl

theorem restrictWord_trans {L M N : ℕ} (hLM : L ≤ M) (hMN : M ≤ N)
    (a : HalfWord N) :
    restrictWord hLM (restrictWord hMN a) = restrictWord (hLM.trans hMN) a := by
  funext i
  rfl

/-- The set represented by a finite Boolean word. -/
def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}

theorem wordSupport_restrictWord {M N : ℕ} (hMN : M ≤ N)
    (a : HalfWord N) :
    wordSupport (restrictWord hMN a) = wordSupport a ∩ Set.Iic M := by
  ext n
  constructor
  · rintro ⟨hn, ha⟩
    refine ⟨⟨lt_of_lt_of_le hn (Nat.succ_le_succ hMN), ?_⟩,
      Nat.le_of_lt_succ hn⟩
    simpa [restrictWord] using ha
  · rintro ⟨⟨hn, ha⟩, hnM⟩
    refine ⟨Nat.lt_succ_of_le hnM, ?_⟩
    simpa [restrictWord] using ha

/-- All-prefix strip admissibility for one finite Boolean word. -/
def HalfStripAdmissible (N : ℕ) (a : HalfWord N) : Prop :=
  a ⟨0, Nat.zero_lt_succ N⟩ = false ∧
  (∀ h : 1 < N + 1, a ⟨1, h⟩ = false) ∧
  ∀ n : ℕ, 1 ≤ n → n ≤ N →
    (1 : ℤ) ≤ integerHalfCarry (wordSupport a) (n - 1) ∧
      integerHalfCarry (wordSupport a) (n - 1) ≤ halfStripBound n

/-- Admissibility is stable under restriction, the key functorial fact needed
by the inverse-system compactness argument. -/
theorem HalfStripAdmissible.restrict {M N : ℕ} (hMN : M ≤ N)
    {a : HalfWord N} (ha : HalfStripAdmissible N a) :
    HalfStripAdmissible M (restrictWord hMN a) := by
  rcases ha with ⟨hzero, hone, hstrip⟩
  refine ⟨hzero, ?_, ?_⟩
  · intro h
    exact hone (lt_of_lt_of_le h (Nat.succ_le_succ hMN))
  · intro n hnpos hnM
    rw [wordSupport_restrictWord]
    rw [integerHalfCarry_inter_Iic_eq_of_succ_le
      (wordSupport a) M (n - 1) (by omega)]
    exact hstrip n hnpos (hnM.trans hMN)

/-- A terminal carry is reachable when some admissible Boolean word has that
carry. -/
def HalfTerminalReachable (N k : ℕ) : Prop :=
  ∃ a : HalfWord N, HalfStripAdmissible N a ∧
    integerHalfCarry (wordSupport a) (N - 1) = k

/-- Full terminal-strip reachability at level `N`. -/
def HalfCarryFullStripReachabilityAt (N : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ halfStripBound N → HalfTerminalReachable N k

/-! ## Exact scalar transition geometry -/

/-- The two children of a parent carry under a fixed proper-divisor
coefficient. -/
def FixedCoeffChild (c h k : ℤ) : Prop :=
  k = 2 * h - c ∨ k = 2 * h - c - 1

/-- Every integer has a unique fixed-coefficient parent and Boolean child
bit.  This is the parity inverse behind interval tiling. -/
theorem fixedCoeffChild_existsUnique (c k : ℤ) :
    ∃! h : ℤ, FixedCoeffChild c h k := by
  by_cases heven : Even (k + c)
  · obtain ⟨q, hq⟩ := heven
    refine ⟨q, Or.inl ?_, ?_⟩
    · omega
    · intro h hh
      rcases hh with hh | hh
      · omega

      · have hodd : Odd (k + c) := by
          refine ⟨h - 1, ?_⟩
          omega
        obtain ⟨r, hr⟩ := hodd
        omega
  · have hodd : Odd (k + c) := Int.not_even_iff_odd.mp heven
    obtain ⟨q, hq⟩ := hodd
    refine ⟨q + 1, Or.inr ?_, ?_⟩
    · omega
    · intro h hh
      rcases hh with hh | hh
      · have heven' : Even (k + c) := by
          refine ⟨h, ?_⟩
          omega
        exact (heven heven').elim
      · omega

/-- The parity inverse for a target inside the new strip has its unique parent
inside the preceding strip.  This is the proof-bearing fixed-coefficient
tiling step, with the square-root headroom discharged explicitly. -/
theorem fixedCoeffChild_existsUnique_parent_in_pred_strip
    {n c k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hkB : k ≤ halfStripBound n) (hc : c ≤ 2 * Nat.sqrt n) :
    ∃! h : ℤ, (1 : ℤ) ≤ h ∧ h ≤ halfStripBound (n - 1) ∧
      FixedCoeffChild c h k := by
  obtain ⟨h, hh, hunique⟩ := fixedCoeffChild_existsUnique (c : ℤ) (k : ℤ)
  have hhead := halfStripBound_add_coeff_le_two_mul_pred hn hc
  have hsum : k + c ≤ 2 * halfStripBound (n - 1) :=
    (Nat.add_le_add_right hkB c).trans hhead
  have hsumZ : (k : ℤ) + c ≤ 2 * halfStripBound (n - 1) := by
    exact_mod_cast hsum
  refine ⟨h, ⟨?_, ?_, hh⟩, ?_⟩
  · rcases hh with hh | hh <;> omega
  · rcases hh with hh | hh <;> omega
  · intro h' hh'
    exact hunique h' hh'.2.2

/-- Child geometry when the half-divisor bit changes at parent `δ`: parents
at or below `δ` have coefficient `c+1`; parents above it have coefficient
`c`. -/
def EvenSeamReachable (δ c k : ℤ) : Prop :=
  (∃ h : ℤ, h ≤ δ ∧ (k = 2 * h - c - 1 ∨ k = 2 * h - c - 2)) ∨
  (∃ h : ℤ, δ < h ∧ (k = 2 * h - c ∨ k = 2 * h - c - 1))

/-- **Exact one-hole theorem.**  The unresolved half-divisor transition
reaches every integer except `2δ-c`; there are no other holes. -/
theorem evenSeamReachable_iff (δ c k : ℤ) :
    EvenSeamReachable δ c k ↔ k ≠ 2 * δ - c := by
  constructor
  · rintro (⟨h, hh, hk | hk⟩ | ⟨h, hh, hk | hk⟩) <;> omega
  · intro hgap
    rcases fixedCoeffChild_existsUnique c k with ⟨h, hh, -⟩
    by_cases hhδ : h ≤ δ
    · left
      rcases hh with hk | hk
      · have : h ≠ δ := by
          intro heq
          apply hgap
          omega
        exact ⟨h + 1, by omega, Or.inr (by omega)⟩
      · exact ⟨h, hhδ, Or.inl (by omega)⟩
    · right
      exact ⟨h, by omega, hh⟩

/-- Endpoint-bearing version of `EvenSeamReachable`.  If a parent with
numerator `T-h` receives child bit `b`, its child numerator is
`2*(T-h)+b`.  The two sides of the seam use fixed coefficients `c+1` and
`c`, respectively. -/
def EvenSeamNumeratorReachable (δ c T k q : ℤ) : Prop :=
  (∃ h : ℤ, h ≤ δ ∧
    ((k = 2 * h - c - 1 ∧ q = 2 * (T - h)) ∨
      (k = 2 * h - c - 2 ∧ q = 2 * (T - h) + 1))) ∨
  (∃ h : ℤ, δ < h ∧
    ((k = 2 * h - c ∧ q = 2 * (T - h)) ∨
      (k = 2 * h - c - 1 ∧ q = 2 * (T - h) + 1)))

/-- **Exact two-sheet normal form.**  Away from the missing carry
`2*δ-c`, the seam has one affine numerator sheet on each side.  Below the
hole its endpoint is `2*T-c-1`; above the hole its endpoint is `2*T-c`. -/
theorem evenSeamNumeratorReachable_iff_twoSheets (δ c T k q : ℤ) :
    EvenSeamNumeratorReachable δ c T k q ↔
      (k < 2 * δ - c ∧ q = (2 * T - c - 1) - k) ∨
      (2 * δ - c < k ∧ q = (2 * T - c) - k) := by
  constructor
  · rintro (⟨h, hh, (⟨hk, hq⟩ | ⟨hk, hq⟩)⟩ |
      ⟨h, hh, (⟨hk, hq⟩ | ⟨hk, hq⟩)⟩)
    · left
      constructor <;> omega
    · left
      constructor <;> omega
    · right
      constructor <;> omega
    · right
      constructor <;> omega
  · rintro (⟨hk, hq⟩ | ⟨hk, hq⟩)
    · have hgap : k ≠ 2 * δ - c := by omega
      have hreach := (evenSeamReachable_iff δ c k).2 hgap
      rcases hreach with ⟨h, hh, hk' | hk'⟩ | ⟨h, hh, hk' | hk'⟩
      · left
        exact ⟨h, hh, Or.inl ⟨hk', by omega⟩⟩
      · left
        exact ⟨h, hh, Or.inr ⟨hk', by omega⟩⟩
      · omega
      · omega
    · have hgap : k ≠ 2 * δ - c := by omega
      have hreach := (evenSeamReachable_iff δ c k).2 hgap
      rcases hreach with ⟨h, hh, hk' | hk'⟩ | ⟨h, hh, hk' | hk'⟩
      · omega
      · omega
      · right
        exact ⟨h, hh, Or.inl ⟨hk', by omega⟩⟩
      · right
        exact ⟨h, hh, Or.inr ⟨hk', by omega⟩⟩

/-- If the seam hole lies below the target strip, every target numerator is
on the upper sheet, so the strip is a single cylinder with endpoint
`2*T-c`. -/
theorem evenSeam_recylindrifies_of_hole_below_strip
    {δ c T : ℤ} {k : ℕ} (hk : 1 ≤ k) (hhole : 2 * δ - c < 1) :
    EvenSeamNumeratorReachable δ c T k ((2 * T - c) - k) := by
  rw [evenSeamNumeratorReachable_iff_twoSheets]
  right
  constructor <;> omega

/-- If the seam hole lies above the target strip, every target numerator is
on the lower sheet, so the strip is a single cylinder with endpoint
`2*T-c-1`. -/
theorem evenSeam_recylindrifies_of_hole_above_strip
    {δ c T : ℤ} {B k : ℕ} (hkB : k ≤ B)
    (hhole : (B : ℤ) < 2 * δ - c) :
    EvenSeamNumeratorReachable δ c T k ((2 * T - c - 1) - k) := by
  rw [evenSeamNumeratorReachable_iff_twoSheets]
  left
  constructor <;> omega

/-- Negative regression fixture: the depth-14 scalar data `δ=2`, `c=1`
misses terminal carry `3` exactly. -/
theorem depth14_evenSeam_three_not_reachable :
    ¬ EvenSeamReachable 2 1 3 := by
  rw [evenSeamReachable_iff]
  simp

/-- Strip-restricted form of the exact one-hole theorem. -/
theorem evenSeamReachable_in_strip_iff
    (B : ℕ) (δ c : ℤ) {k : ℕ} (hk : 1 ≤ k) (hkB : k ≤ B) :
    EvenSeamReachable δ c k ↔
      k ∈ Finset.Icc 1 B ∧ (k : ℤ) ≠ 2 * δ - c := by
  simp only [evenSeamReachable_iff, Finset.mem_Icc, hk, hkB, true_and]

/-- The coordinate bridge asserting that one actual even transition is
exactly the scalar seam model.  The cylinder induction is expected to produce
this interface whenever exponent `d` is unresolved at depth `2d-1`. -/
def IsCanonicalEvenSeam (d : ℕ) (δ c : ℤ) : Prop :=
  ∀ k : ℕ, HalfTerminalReachable (2 * d) k ↔
    1 ≤ k ∧ k ≤ halfStripBound (2 * d) ∧ EvenSeamReachable δ c k

/-- The open arithmetic obligation: every post-base canonical half-divisor
seam must miss the target strip. -/
def HalfCarryEvenSeamEscape : Prop :=
  ∀ d : ℕ, 10 ≤ d → ∀ δ c : ℤ, IsCanonicalEvenSeam d δ c →
    2 * δ - c < 1 ∨
      (halfStripBound (2 * d) : ℤ) < 2 * δ - c

/-- Producer interface asserting that every post-base even depth admits the
canonical one-seam coordinate.  This is deliberately separate from seam
escape: a solver may construct the coordinate and prove its scalar escape by
different arguments. -/
def HalfCarryCanonicalEvenSeamSupply : Prop :=
  ∀ d : ℕ, 10 ≤ d → ∃ δ c : ℤ, IsCanonicalEvenSeam d δ c

/-- Once a canonical seam is outside the strip, the exact one-hole theorem
immediately restores full terminal reachability at that even level. -/
theorem fullStripAt_even_of_canonicalSeam_escape
    {d : ℕ} {δ c : ℤ} (hcanonical : IsCanonicalEvenSeam d δ c)
    (hescape : 2 * δ - c < 1 ∨
      (halfStripBound (2 * d) : ℤ) < 2 * δ - c) :
    HalfCarryFullStripReachabilityAt (2 * d) := by
  unfold HalfCarryFullStripReachabilityAt
  unfold IsCanonicalEvenSeam at hcanonical
  intro k hk hkB
  have hseam : EvenSeamReachable δ c k := by
    rw [evenSeamReachable_iff]
    rcases hescape with hlow | hhigh <;> omega
  exact (hcanonical k).2 ⟨hk, hkB, hseam⟩

/-- The two independent even-level producers compose to full terminal-strip
reachability at every post-base even depth. -/
theorem fullStripAt_even_of_evenSeamSupply_escape
    (hcanonical : HalfCarryCanonicalEvenSeamSupply)
    (hescape : HalfCarryEvenSeamEscape)
    {d : ℕ} (hd : 10 ≤ d) :
    HalfCarryFullStripReachabilityAt (2 * d) := by
  obtain ⟨δ, c, hseam⟩ := hcanonical d hd
  exact fullStripAt_even_of_canonicalSeam_escape hseam
    (hescape d hd δ c hseam)

/-! ## Generic inverse-system compactness -/

/-- A coherent sequence of nonempty finite Boolean-prefix families has an
infinite Boolean diagonal whose every finite prefix belongs to the family. -/
theorem exists_bool_sequence_of_prefix_closed_finite_words
    (Good : ∀ N : ℕ, HalfWord N → Prop)
    (hrestrict : ∀ {M N : ℕ} (hMN : M ≤ N) {a : HalfWord N},
      Good N a → Good M (restrictWord hMN a))
    (hnonempty : ∀ N : ℕ, ∃ a : HalfWord N, Good N a) :
    ∃ a : ℕ → Bool, ∀ N : ℕ,
      Good N (fun i ↦ a i) := by
  let α : ℕ → Type := fun N ↦ {a : HalfWord N // Good N a}
  let π : {M N : ℕ} → M ≤ N → α N → α M :=
    fun {M N} hMN a ↦ ⟨restrictWord hMN a.1, hrestrict hMN a.2⟩
  letI : ∀ N, Nonempty (α N) := fun N ↦
    let ⟨a, ha⟩ := hnonempty N
    ⟨⟨a, ha⟩⟩
  have hπrefl : ∀ ⦃N⦄ (a : α N), π (le_refl N) a = a := by
    intro N a
    apply Subtype.ext
    exact restrictWord_refl a.1
  have hπtrans : ∀ ⦃L M N⦄ (hLM : L ≤ M) (hMN : M ≤ N) (a : α N),
      π hLM (π hMN a) = π (hLM.trans hMN) a := by
    intro L M N hLM hMN a
    apply Subtype.ext
    exact restrictWord_trans hLM hMN a.1
  have hfin : ∀ N (a : α N),
      {b : α (N + 1) | π (Nat.le_add_right N 1) b = a}.Finite := by
    intro N a
    exact Set.toFinite _
  obtain ⟨f, hf⟩ :=
    exists_seq_forall_proj_of_forall_finite π hπrefl hπtrans hfin
  let a : ℕ → Bool := fun n ↦ (f n).1 ⟨n, Nat.lt_succ_self n⟩
  refine ⟨a, fun N ↦ ?_⟩
  have hword : (fun i : Fin (N + 1) ↦ a i) = (f N).1 := by
    funext i
    have hcoh := congrArg (fun w : α i ↦ w.1 ⟨i, Nat.lt_succ_self i⟩)
      (hf (Nat.le_of_lt_succ i.isLt) : π (Nat.le_of_lt_succ i.isLt) (f N) = f i)
    exact hcoh.symm
  rw [hword]
  exact (f N).2

/-- Nonempty admissible words at every height yield one infinite Boolean word
whose every finite prefix is strip-admissible. -/
theorem exists_infinite_halfStripBranch
    (hfinite : ∀ N : ℕ, ∃ a : HalfWord N, HalfStripAdmissible N a) :
    ∃ a : ℕ → Bool, ∀ N : ℕ,
      HalfStripAdmissible N (fun i ↦ a i) :=
  exists_bool_sequence_of_prefix_closed_finite_words
    HalfStripAdmissible
    (fun {_ _} hMN {_} ha ↦
      HalfStripAdmissible.restrict hMN ha) hfinite

/-- Full terminal-strip reachability at every positive height supplies the
nonempty levels required by compactness. -/
theorem exists_infinite_halfStripBranch_of_fullStrip
    (hfull : ∀ N : ℕ, 1 ≤ N → HalfCarryFullStripReachabilityAt N) :
    ∃ a : ℕ → Bool, ∀ N : ℕ,
      HalfStripAdmissible N (fun i ↦ a i) := by
  apply exists_infinite_halfStripBranch
  intro N
  by_cases hN : N = 0
  · subst N
    refine ⟨fun _ ↦ false, ?_⟩
    refine ⟨rfl, ?_, ?_⟩
    · intro h
      omega
    · intro n hn hn0
      omega
  · obtain ⟨a, ha, -⟩ :=
      hfull N (by omega) 1 (by omega) (by simp [halfStripBound])
    exact ⟨a, ha⟩

/-- One admissible base level together with full terminal strips from that
level onward supplies the nonempty finite levels required by compactness.
Earlier levels are obtained by restricting the base word. -/
theorem exists_infinite_halfStripBranch_of_eventualFullStrip
    (N₀ : ℕ)
    (hbase : ∃ a : HalfWord N₀, HalfStripAdmissible N₀ a)
    (hfull : ∀ N : ℕ, N₀ ≤ N → HalfCarryFullStripReachabilityAt N) :
    ∃ a : ℕ → Bool, ∀ N : ℕ,
      HalfStripAdmissible N (fun i ↦ a i) := by
  apply exists_infinite_halfStripBranch
  intro N
  by_cases hN : N ≤ N₀
  · obtain ⟨a, ha⟩ := hbase
    exact ⟨restrictWord hN a, ha.restrict hN⟩
  · obtain ⟨a, ha, -⟩ :=
      hfull N (by omega) 1 (by omega) (by simp [halfStripBound])
    exact ⟨a, ha⟩

/-! ## From a coherent branch to exact equality -/

/-- The support selected by an infinite Boolean word. -/
def boolSupport (a : ℕ → Bool) : Set ℕ :=
  {n | a n = true}

/-- A finite word cut from an infinite Boolean word represents exactly the
intersection of its support with the corresponding initial interval. -/
theorem wordSupport_sequence_eq_inter_Iic (a : ℕ → Bool) (N : ℕ) :
    wordSupport (fun i : Fin (N + 1) ↦ a i) =
      boolSupport a ∩ Set.Iic N := by
  ext n
  constructor
  · rintro ⟨hn, ha⟩
    exact ⟨ha, Nat.le_of_lt_succ hn⟩
  · rintro ⟨ha, hn⟩
    exact ⟨Nat.lt_succ_of_le hn, ha⟩

/-- Every coherent finite-prefix strip bound transfers to the global support
carry at the same level. -/
theorem halfStripBranch_integerHalfCarry_bounds
    (a : ℕ → Bool)
    (hbranch : ∀ N : ℕ, HalfStripAdmissible N (fun i ↦ a i))
    (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℤ) ≤ integerHalfCarry (boolSupport a) (n - 1) ∧
      integerHalfCarry (boolSupport a) (n - 1) ≤ halfStripBound n := by
  have hstrip := (hbranch n).2.2 n hn le_rfl
  rw [wordSupport_sequence_eq_inter_Iic] at hstrip
  rw [integerHalfCarry_inter_Iic_eq_of_succ_le
    (boolSupport a) n (n - 1) (by omega)] at hstrip
  exact hstrip

/-- The exponent-one guard carried by every admissible branch. -/
theorem one_not_mem_boolSupport_of_halfStripBranch
    (a : ℕ → Bool)
    (hbranch : ∀ N : ℕ, HalfStripAdmissible N (fun i ↦ a i)) :
    1 ∉ boolSupport a := by
  intro hmem
  have hone := (hbranch 1).2.1 (show 1 < 1 + 1 by omega)
  change a 1 = true at hmem
  simp [hmem] at hone

/-- The index-zero guard carried by every admissible branch. -/
theorem zero_not_mem_boolSupport_of_halfStripBranch
    (a : ℕ → Bool)
    (hbranch : ∀ N : ℕ, HalfStripAdmissible N (fun i ↦ a i)) :
    0 ∉ boolSupport a := by
  intro hmem
  have hzero := (hbranch 0).1
  change a 0 = true at hmem
  simp [hmem] at hzero

/-- A coherent positive square-root-strip branch has exact support-series
value `1/2`.  This is the compactness consumer: it reuses the existing
denominator-two carry factorisation and temperedness theorem. -/
theorem support_half_of_infinite_halfStripBranch
    (a : ℕ → Bool)
    (hbranch : ∀ N : ℕ, HalfStripAdmissible N (fun i ↦ a i)) :
    erdosSupportSeries 2 (boolSupport a) = (1 : ℝ) / 2 := by
  let A := boolSupport a
  let U : ℕ → ℤ := affineBinaryOrbit
    (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1
  have hone : 1 ∉ A := one_not_mem_boolSupport_of_halfStripBranch a hbranch
  apply (support_half_iff_affineBinaryOrbit_tempered A).2
  change IsTemperedBinaryOrbit (supportCoeff A) 2 U
  refine ⟨?_, ?_⟩
  · intro N
    rfl
  · apply tendsto_div_pow_zero_of_nonnegative_sqrt_bound 2 U
    · intro N
      cases N with
      | zero => simp [U]
      | succ N =>
          have hpos :=
            (halfStripBranch_integerHalfCarry_bounds a hbranch (N + 1) (by omega)).1
          have hpos' : (1 : ℤ) ≤ integerHalfCarry A N := by
            simpa [A] using hpos
          have hfactor : U (N + 1) = 2 * integerHalfCarry A N := by
            simpa [U, integerHalfCarry] using
              halfDenominatorCarry_eq_two_mul_integerCarry A hone N
          rw [hfactor]
          omega
    · intro N
      cases N with
      | zero => norm_num [U]
      | succ N =>
          have hupper :=
            (halfStripBranch_integerHalfCarry_bounds a hbranch (N + 1) (by omega)).2
          have hupperR : (integerHalfCarry A N : ℝ) ≤
              (halfStripBound (N + 1) : ℕ) := by
            exact_mod_cast hupper
          have hsqrt : (Nat.sqrt (N + 1) : ℝ) ≤
              Real.sqrt ((N : ℝ) + 1) := by
            simpa only [Nat.cast_add, Nat.cast_one] using
              (Real.nat_sqrt_le_real_sqrt (a := N + 1))
          have hstripR : (halfStripBound (N + 1) : ℝ) ≤
              2 * Real.sqrt ((N : ℝ) + 1) + 4 := by
            unfold halfStripBound
            push_cast
            gcongr
          have hcarryR : (integerHalfCarry A N : ℝ) ≤
              2 * Real.sqrt ((N : ℝ) + 1) + 4 :=
            hupperR.trans hstripR
          have hfactor : U (N + 1) = 2 * integerHalfCarry A N := by
            simpa [U, integerHalfCarry] using
              halfDenominatorCarry_eq_two_mul_integerCarry A hone N
          rw [hfactor]
          push_cast
          simpa only [Nat.cast_add, Nat.cast_one] using
            (mul_le_mul_of_nonneg_left hcarryR (by norm_num : (0 : ℝ) ≤ 2))

/-- A finite positive-index support cannot have support-series value `1/2`,
because its audited reduced denominator is odd. -/
theorem finite_boolSupport_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2 := by
  classical
  let F : Finset ℕ := hfinite.toFinset
  have hFA : (↑F : Set ℕ) = A := by
    dsimp [F]
    exact hfinite.coe_toFinset
  have hFzero : 0 ∉ F := by
    intro hmem
    apply hzero
    rw [← hFA]
    simpa using hmem
  intro hhalf
  have hcast : ((finiteErdosSum F 2 : ℚ) : ℝ) = (1 : ℝ) / 2 := by
    rw [← erdosSupportSeries_finset_eq_cast_finiteErdosSum F, hFA]
    exact hhalf
  have hrat : finiteErdosSum F 2 = (1 : ℚ) / 2 := by
    apply Rat.cast_injective (α := ℝ)
    simpa using hcast
  have hodd := finiteErdosSum_den_odd F hFzero
  rw [hrat] at hodd
  obtain ⟨k, hk⟩ := hodd
  norm_num at hk
  omega

/-! ## Möbius-centred carry intake

The exact signed baseline `s₁ = 0`, `sₙ = -μ(n)` for `n ≥ 2` has divisor
sum zero at row one and one at every later row.  Subtracting that baseline
from a Boolean support therefore centres the canonical half carry at zero.

This is an adapter into the existing half-carry consumer, not a new carry
model.  The remaining producer obligation is exactly the subexponential
boundary for `mobiusCenteredHalfCarry`; no bounded or logarithmic envelope
is frozen into the theorem statement.
-/

/-- The signed Möbius baseline behind the exact representation of `1/2`.
The exceptional value at one removes the terminating binary digit. -/
noncomputable def signedMobiusBaseline (n : ℕ) : ℤ :=
  if n = 1 then 0 else -ArithmeticFunction.moebius n

/-- The signed baseline has the target binary coefficient word: zero in row
one and one in every positive row after it. -/
theorem sum_divisors_signedMobiusBaseline (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, signedMobiusBaseline d) =
      if n = 1 then 0 else 1 := by
  classical
  by_cases hn1 : n = 1
  · subst n
    norm_num [signedMobiusBaseline]
  · rw [if_neg hn1]
    have hmu := MersenneLambertLadder.sum_divisors_moebius n
    rw [if_neg hn1] at hmu
    calc
      (∑ d ∈ n.divisors, signedMobiusBaseline d) =
          ∑ d ∈ n.divisors,
            (-ArithmeticFunction.moebius d + if d = 1 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hd1 : d = 1
        · subst d
          simp [signedMobiusBaseline]
        · simp [signedMobiusBaseline, hd1]
      _ = -(∑ d ∈ n.divisors, ArithmeticFunction.moebius d) + 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hmu]
        simp [hn.ne']
      _ = 1 := by rw [hmu]; simp

/-- The canonical integer half carry measured relative to the signed
Möbius solution.  Index `N` corresponds to the packet's state `e_{N+1}`. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1

@[simp] theorem mobiusCenteredHalfCarry_zero (A : Set ℕ) :
    mobiusCenteredHalfCarry A 0 = 0 := by
  simp [mobiusCenteredHalfCarry]

/-- Exact centred recurrence.  Its forcing term is the Boolean divisor
coefficient minus the signed baseline coefficient one. -/
theorem mobiusCenteredHalfCarry_succ (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 1) =
      2 * mobiusCenteredHalfCarry A N + 1 -
        (supportCoeff A (N + 2) : ℤ) := by
  rw [mobiusCenteredHalfCarry, integerHalfCarry_succ,
    mobiusCenteredHalfCarry]
  ring

/-- Coboundary normal form for Booleanisation relative to the signed
Möbius baseline. -/
theorem mobiusCenteredHalfCarry_coboundary (A : Set ℕ) (N : ℕ) :
    (supportCoeff A (N + 2) : ℤ) - 1 =
      2 * mobiusCenteredHalfCarry A N -
        mobiusCenteredHalfCarry A (N + 1) := by
  rw [mobiusCenteredHalfCarry_succ]
  ring

/-- The same coboundary with the signed divisor baseline left visible.
This is the literal `D = 2e - e⁺` intake equation from the returned packet. -/
theorem boolean_sub_signedMobiusBaseline_eq_centeredCoboundary
    (A : Set ℕ) (N : ℕ) :
    (supportCoeff A (N + 2) : ℤ) -
        (∑ d ∈ (N + 2).divisors, signedMobiusBaseline d) =
      2 * mobiusCenteredHalfCarry A N -
        mobiusCenteredHalfCarry A (N + 1) := by
  have hbaseline := sum_divisors_signedMobiusBaseline (N + 2) (by omega)
  rw [if_neg (by omega)] at hbaseline
  rw [hbaseline]
  exact mobiusCenteredHalfCarry_coboundary A N

/-- Any subexponential Möbius-centred carry already closes exact
half-membership through the existing canonical denominator-two orbit. -/
theorem support_half_of_mobiusCenteredHalfCarry_tempered
    (A : Set ℕ) (hone : 1 ∉ A)
    (htempered : Tendsto
      (fun N : ℕ ↦
        (mobiusCenteredHalfCarry A N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0)) :
    erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  apply (support_half_iff_affineBinaryOrbit_tempered A).2
  let U : ℕ → ℤ := affineBinaryOrbit
    (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1
  change IsTemperedBinaryOrbit (supportCoeff A) 2 U
  refine ⟨fun _ ↦ rfl, ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hgeom : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hsum : Tendsto
      (fun N : ℕ ↦
        (mobiusCenteredHalfCarry A N : ℝ) / (2 : ℝ) ^ N +
          (1 : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    simpa using htempered.add hgeom
  have hfunctions :
      (fun N : ℕ ↦ (U (N + 1) : ℝ) / (2 : ℝ) ^ (N + 1)) =
        (fun N : ℕ ↦
          (mobiusCenteredHalfCarry A N : ℝ) / (2 : ℝ) ^ N +
            (1 : ℝ) / (2 : ℝ) ^ N) := by
    funext N
    change
      ((affineBinaryOrbit
          (fun n : ℕ ↦ ((2 * supportCoeff A n : ℕ) : ℤ)) 1 (N + 1) : ℤ) : ℝ) /
          (2 : ℝ) ^ (N + 1) = _
    rw [halfDenominatorCarry_eq_two_mul_integerCarry A hone N]
    change ((2 * integerHalfCarry A N : ℤ) : ℝ) /
        (2 : ℝ) ^ (N + 1) = _
    push_cast
    rw [pow_succ]
    simp only [mobiusCenteredHalfCarry]
    push_cast
    ring
  rw [hfunctions]
  exact hsum

/-- The exact endpoint wanted by the construction lane: a normalized
support with tempered centred carry is automatically infinite and sums to
`1/2`. -/
theorem infinite_support_half_of_mobiusCenteredHalfCarry_tempered
    (A : Set ℕ) (hzero : 0 ∉ A) (hone : 1 ∉ A)
    (htempered : Tendsto
      (fun N : ℕ ↦
        (mobiusCenteredHalfCarry A N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0)) :
    A.Infinite ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  have hhalf :=
    support_half_of_mobiusCenteredHalfCarry_tempered A hone htempered
  refine ⟨?_, hhalf⟩
  intro hfinite
  exact finite_boolSupport_ne_half A hfinite hzero hhalf

/-- Greedy-specialized endpoint.  A continuation now needs to prove only
the displayed subexponential centred-carry limit for the canonical greedy
support; zero/one normalization, exact half-membership, and infinitude are
discharged here. -/
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_tempered
    (htempered : Tendsto
      (fun N : ℕ ↦
        (mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) / (2 : ℝ) ^ N)
      atTop (nhds 0)) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  apply infinite_support_half_of_mobiusCenteredHalfCarry_tempered
    (greedyMersenneSupport (1 / 2 : ℝ))
    (zero_not_mem_greedyMersenneSupport _)
  · intro hone
    have htake :=
      (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) 0).mp (by
        simpa using hone)
    norm_num [mersenneWeight, greedyMersenneRemainder] at htake
  · exact htempered

/-- Pointwise square-root control is a concrete sufficient producer for the
Möbius-centred endpoint.  This exposes the existing generic carry-growth
theorem directly at the exact support-series consumer. -/
theorem infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
    (A : Set ℕ) (hzero : 0 ∉ A) (hone : 1 ∉ A)
    (hnonneg : ∀ N : ℕ, 0 ≤ mobiusCenteredHalfCarry A N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry A N : ℝ) ≤
        2 * Real.sqrt (N : ℝ) + 4) :
    A.Infinite ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  apply infinite_support_half_of_mobiusCenteredHalfCarry_tempered
    A hzero hone
  apply tendsto_div_pow_zero_of_nonnegative_sqrt_bound 1
    (mobiusCenteredHalfCarry A) hnonneg
  intro N
  simpa using hbound N

/-- Greedy-facing square-root endpoint.  The open construction problem is
now expressible as the two pointwise carry inequalities witnessed by all
current finite runs, rather than as an abstract filter limit. -/
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
    (hnonneg : ∀ N : ℕ,
      0 ≤ mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  apply infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
    (greedyMersenneSupport (1 / 2 : ℝ))
    (zero_not_mem_greedyMersenneSupport _)
  · intro hone
    have htake :=
      (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) 0).mp (by
        simpa using hone)
    norm_num [mersenneWeight, greedyMersenneRemainder] at htake
  · exact hnonneg
  · exact hbound

/-! ## Unconditional nonnegativity of the greedy centred carry

The residual identity `2^(N+1) · (1/2 - S_A) = K_N - T_A(N+1)` writes the
integer half carry as a scaled value defect plus the future-multiple
coefficient tail.  For the canonical greedy support the defect is
nonnegative because greedy prefix sums never overshoot their target, and
the tail is strictly positive because exponent two is taken, so the carry
is a positive integer.  This discharges the first of the two pointwise
producer obligations of
`greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound`
unconditionally; only the upper bound remains open.
-/

/-- Exact bridge: the integer half carry equals the scaled half-residual
plus the analytic support-coefficient tail. -/
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1) := by
  have hres :=
    halfSupportSeries_residual_scaled_eq_affineCarry_sub_tail A (N + 1)
  rw [halfDenominatorCarry_eq_two_mul_integerCarry A hone N] at hres
  have hfold : affineBinaryOrbit
      (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1 N =
        integerHalfCarry A N := rfl
  rw [hfold] at hres
  push_cast at hres
  linarith

/-- Greedy prefix sums never overshoot, so the greedy support value is at
most its target. -/
theorem erdosSupportSeries_greedyMersenneSupport_le {x : ℝ} (hx : 0 ≤ x) :
    erdosSupportSeries 2 (greedyMersenneSupport x) ≤ x := by
  rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
  have htoSum : Tendsto
      (fun n : ℕ ↦ ∑ k ∈ Finset.range n,
        Set.indicator (greedyMersenneSupport x) mersenneWeight (k + 1))
      atTop
      (nhds (positiveMersenneSupportValue (greedyMersenneSupport x))) := by
    simpa [positiveMersenneSupportValue] using
      (summable_positiveMersenneSupportIndicator
        (greedyMersenneSupport x)).tendsto_sum_tsum_nat
  refine le_of_tendsto htoSum (Filter.Eventually.of_forall fun n ↦ ?_)
  have hprefix := greedyMersenne_prefix_add_remainder x n
  have hrem := greedyMersenneRemainder_nonneg hx n
  linarith

/-- The greedy half orbit takes exponent two immediately. -/
theorem two_mem_greedyMersenneSupport_half :
    2 ∈ greedyMersenneSupport (1 / 2 : ℝ) := by
  have hrem1 : greedyMersenneRemainder (1 / 2 : ℝ) 1 = 1 / 2 := by
    rw [greedyMersenneRemainder_succ]
    norm_num [mersenneWeight]
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  rw [h2, succ_mem_greedyMersenneSupport_iff, hrem1]
  norm_num [mersenneWeight]

/-- **Unconditional nonnegativity of the greedy centred carry.**  The first
pointwise producer obligation for exact greedy half-membership holds with
no hypotheses: greedy prefix sums cannot overshoot `1/2`, the pending
future-multiple tail of the taken exponents is strictly positive, and the
carry is an integer, so it is at least one. -/
theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N := by
  have hone : 1 ∉ greedyMersenneSupport (1 / 2 : ℝ) := by
    intro hone
    have htake :=
      (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) 0).mp (by
        simpa using hone)
    norm_num [mersenneWeight, greedyMersenneRemainder] at htake
  have hid := integerHalfCarry_eq_scaled_residual_add_tail
    (greedyMersenneSupport (1 / 2 : ℝ)) hone N
  have hS : erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) ≤
      1 / 2 :=
    erdosSupportSeries_greedyMersenneSupport_le (by norm_num)
  have htail : 0 < binaryCoeffTail
      (supportCoeff (greedyMersenneSupport (1 / 2 : ℝ))) (N + 1) :=
    binaryCoeffTail_supportCoeff_pos_of_exists_pos_mem
      (greedyMersenneSupport (1 / 2 : ℝ))
      ⟨2, by norm_num, two_mem_greedyMersenneSupport_half⟩ (N + 1)
  have hterm : (0 : ℝ) ≤ (2 : ℝ) ^ (N + 1) *
      ((1 : ℝ) / 2 -
        erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ))) :=
    mul_nonneg (by positivity) (by linarith)
  have hKpos : (0 : ℝ) <
      (integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) := by
    rw [hid]
    linarith
  have hKint : 0 < integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N := by
    exact_mod_cast hKpos
  unfold mobiusCenteredHalfCarry
  omega

/-- **Producer reduction.**  With nonnegativity discharged unconditionally,
the sole remaining producer obligation for exact greedy half-membership is
the pointwise square-root upper bound on the centred carry. -/
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 :=
  greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
    greedy_mobiusCenteredHalfCarry_nonneg hbound

/-- The support of a coherent half-strip branch is necessarily infinite. -/
theorem boolSupport_infinite_of_halfStripBranch
    (a : ℕ → Bool)
    (hbranch : ∀ N : ℕ, HalfStripAdmissible N (fun i ↦ a i)) :
    (boolSupport a).Infinite := by
  intro hfinite
  exact finite_boolSupport_ne_half (boolSupport a) hfinite
    (zero_not_mem_boolSupport_of_halfStripBranch a hbranch)
    (support_half_of_infinite_halfStripBranch a hbranch)

/-- **Conditional decision theorem.**  Full finite reachability at every
positive level yields an infinite support with exact value `1/2`.  Thus the
remaining mathematical work is entirely on the finite reachability side,
whose only scalar defect in the canonical cylinder coordinate is the even
seam isolated above. -/
theorem exists_infinite_support_half_of_fullStrip
    (hfull : ∀ N : ℕ, 1 ≤ N → HalfCarryFullStripReachabilityAt N) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  obtain ⟨a, hbranch⟩ := exists_infinite_halfStripBranch_of_fullStrip hfull
  exact ⟨boolSupport a,
    boolSupport_infinite_of_halfStripBranch a hbranch,
    support_half_of_infinite_halfStripBranch a hbranch⟩

/-- **Eventual full-strip consumer.**  It is enough to have one admissible
base level and full terminal-strip reachability from that level onward.  In
particular, finite holes below the base level do not obstruct the inverse-
system construction. -/
theorem exists_infinite_support_half_of_eventualFullStrip
    (N₀ : ℕ)
    (hbase : ∃ a : HalfWord N₀, HalfStripAdmissible N₀ a)
    (hfull : ∀ N : ℕ, N₀ ≤ N → HalfCarryFullStripReachabilityAt N) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  obtain ⟨a, hbranch⟩ :=
    exists_infinite_halfStripBranch_of_eventualFullStrip N₀ hbase hfull
  exact ⟨boolSupport a,
    boolSupport_infinite_of_halfStripBranch a hbranch,
    support_half_of_infinite_halfStripBranch a hbranch⟩

/-- Minimal compactness-facing producer: admissible finite words exist at
cofinally many levels.  Restriction then supplies a nonempty admissible family
at every earlier level. -/
def HalfCarryCofinalAdmissibility : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    ∃ a : HalfWord M, HalfStripAdmissible M a

/-- Cofinal finite admissibility is already enough for König compactness and
an infinite support summing exactly to `1/2`. -/
theorem exists_infinite_support_half_of_cofinalAdmissibility
    (hcofinal : HalfCarryCofinalAdmissibility) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  have hfinite : ∀ N : ℕ, ∃ a : HalfWord N, HalfStripAdmissible N a := by
    intro N
    obtain ⟨M, hNM, a, ha⟩ := hcofinal N
    exact ⟨restrictWord hNM a, ha.restrict hNM⟩
  obtain ⟨a, hbranch⟩ := exists_infinite_halfStripBranch hfinite
  exact ⟨boolSupport a,
    boolSupport_infinite_of_halfStripBranch a hbranch,
    support_half_of_infinite_halfStripBranch a hbranch⟩

/-- An exact one-hole even seam always leaves at least one of carries `1` and
`2`, so canonical seam supply gives admissible words at cofinally many levels. -/
theorem cofinalAdmissibility_of_canonicalEvenSeamSupply
    (hcanonical : HalfCarryCanonicalEvenSeamSupply) :
    HalfCarryCofinalAdmissibility := by
  intro N
  let d := N + 10
  obtain ⟨δ, c, hseam⟩ := hcanonical d (by simp [d])
  let k : ℕ := if 2 * δ - c = 1 then 2 else 1
  have hkpos : 1 ≤ k := by
    simp only [k]
    split_ifs <;> omega
  have hkB : k ≤ halfStripBound (2 * d) := by
    simp only [k]
    split_ifs <;> simp [halfStripBound]
  have hreach : EvenSeamReachable δ c k := by
    rw [evenSeamReachable_iff]
    simp only [k]
    split_ifs <;> omega
  obtain ⟨w, hw, _⟩ :=
    (hseam k).2 ⟨hkpos, hkB, hreach⟩
  have hNd : N ≤ 2 * d := by
    dsimp [d]
    omega
  exact ⟨2 * d, hNd, w, hw⟩

/-- **One-hole seam consumer.**  Canonical even-seam supply alone gives
cofinally many nonempty admissible levels.  The cofinal compactness consumer
then produces an infinite support.  Neither seam escape nor a separate
odd-level full-strip theorem is needed for this existence conclusion. -/
theorem exists_infinite_support_half_of_canonicalEvenSeamSupply
    (hcanonical : HalfCarryCanonicalEvenSeamSupply) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_cofinalAdmissibility
    (cofinalAdmissibility_of_canonicalEvenSeamSupply hcanonical)

/-- Solver-facing fan-in for the seam route.  A canonical coordinate and
scalar escape settle every even level from `20` onward; an independent odd
level producer and one admissible depth-`20` base then feed the existing
inverse-system consumer. -/
theorem exists_infinite_support_half_of_evenSeamSupply_escape
    (hcanonical : HalfCarryCanonicalEvenSeamSupply)
    (hescape : HalfCarryEvenSeamEscape)
    (hodd : ∀ d : ℕ, 10 ≤ d →
      HalfCarryFullStripReachabilityAt (2 * d + 1))
    (hbase : ∃ a : HalfWord 20, HalfStripAdmissible 20 a) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  apply exists_infinite_support_half_of_eventualFullStrip 20 hbase
  intro N hN
  rcases Nat.even_or_odd N with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · rw [show d + d = 2 * d by omega]
    exact fullStripAt_even_of_evenSeamSupply_escape hcanonical hescape (by omega)
  · exact hodd d (by omega)

#print axioms integerHalfCarry_insert_future_eq
#print axioms evenSeamNumeratorReachable_iff_twoSheets
#print axioms evenSeam_recylindrifies_of_hole_below_strip
#print axioms evenSeam_recylindrifies_of_hole_above_strip
#print axioms infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
#print axioms greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
#print axioms greedy_mobiusCenteredHalfCarry_nonneg
#print axioms greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
#print axioms fullStripAt_even_of_evenSeamSupply_escape
#print axioms exists_infinite_support_half_of_cofinalAdmissibility
#print axioms cofinalAdmissibility_of_canonicalEvenSeamSupply
#print axioms exists_infinite_support_half_of_canonicalEvenSeamSupply
#print axioms exists_infinite_support_half_of_evenSeamSupply_escape

end Erdos249257.HalfCarryReachability
