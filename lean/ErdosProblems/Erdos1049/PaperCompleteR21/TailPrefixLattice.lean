import Mathlib.LinearAlgebra.FreeModule.Int
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

/-!
# Erdős #1049: the prefix lattice of the tails

Paper restatement of `long1049:res:tail-lattice` (the proposition "the prefix lattice of the
tails" in the lattice section of the #1049 reasoning paper).

For coprime `a > b ≥ 1` the partial sums `S_m(b/a) = ∑_{r ≤ m} (b/a)^r / (1 - (b/a)^r)` are
written in lowest terms as `P_m / Q_m`, `Q_m > 0`; `(Q_m, P_m)` is the primitive integer row
of the `m`th tail.  The main theorem `tail_prefix_lattice` proves every clause of the
proposition: `Q_m` is coprime to `ab`, `b ∣ P_m`, the span of every prefix containing
`m = 0, 1` is `ℤ × bℤ`, its Smith invariants are `1, b`, the gcd of the `2 × 2` minors is
`b`, the image modulo `D ≥ 1` has `D² / gcd(b, D)` elements, and a nonzero rational weight
leaves the primitive row of a tail unchanged up to sign.

The Smith invariants are stated with Mathlib's `Module.Basis.SmithNormalForm`, which does not
impose the divisibility chain; the theorem therefore gives existence of the diagonal `(1, b)`,
that every Smith normal form has two entries, and uniqueness up to units under `d₁ ∣ d₂`.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21.TailLattice

open Finset

/-! ### The tails and their rows -/

/-- The partial sum `S_m(b/a) = ∑_{r ≤ m} (b/a)^r / (1 - (b/a)^r)`, the sum running over
`1 ≤ r ≤ m` (so `S_0 = 0`). -/
def tailPartialSum (a b m : ℕ) : ℚ :=
  ∑ r ∈ Icc 1 m, ((b : ℚ) / a) ^ r / (1 - ((b : ℚ) / a) ^ r)

/-- `P_m`: the numerator of `S_m(b/a)` written in lowest terms. -/
def tailP (a b m : ℕ) : ℤ := (tailPartialSum a b m).num

/-- `Q_m > 0`: the denominator of `S_m(b/a)` written in lowest terms. -/
def tailQ (a b m : ℕ) : ℤ := ((tailPartialSum a b m).den : ℤ)

/-- The integer row `(Q_m, P_m)` of the `m`th tail. -/
def tailRow (a b m : ℕ) : ℤ × ℤ := (tailQ a b m, tailP a b m)

/-- The prefix lattice `span_ℤ {(Q_m, P_m) : 0 ≤ m < M}`. -/
def tailPrefixLattice (a b M : ℕ) : Submodule ℤ (ℤ × ℤ) :=
  Submodule.span ℤ (tailRow a b '' Set.Iio M)

/-- The `2 × 2` minor `Q_i P_j - P_i Q_j` of the rows `i` and `j`. -/
def tailMinor (a b i j : ℕ) : ℤ := tailQ a b i * tailP a b j - tailP a b i * tailQ a b j

/-- Reduction modulo `D` of an integer row. -/
def rowModD (D : ℕ) (v : ℤ × ℤ) : ZMod D × ZMod D := ((v.1 : ZMod D), (v.2 : ZMod D))

/-! ### A common denominator -/

/-- The common denominator `∏_{r ≤ m} (a^r - b^r)`. -/
def tailDen (a b : ℕ) : ℕ → ℤ
  | 0 => 1
  | m + 1 => tailDen a b m * ((a : ℤ) ^ (m + 1) - (b : ℤ) ^ (m + 1))

/-- The numerator of `S_m(b/a)` over the common denominator `tailDen`. -/
def tailNum (a b : ℕ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => tailNum a b m * ((a : ℤ) ^ (m + 1) - (b : ℤ) ^ (m + 1)) +
      (b : ℤ) ^ (m + 1) * tailDen a b m

section

variable {a b : ℕ}

lemma tailNum_succ (m : ℕ) : tailNum a b (m + 1) =
    tailNum a b m * ((a : ℤ) ^ (m + 1) - (b : ℤ) ^ (m + 1)) +
      (b : ℤ) ^ (m + 1) * tailDen a b m := rfl

lemma tailDen_succ (m : ℕ) : tailDen a b (m + 1) =
    tailDen a b m * ((a : ℤ) ^ (m + 1) - (b : ℤ) ^ (m + 1)) := rfl

lemma pow_sub_pow_pos (hba : b < a) {r : ℕ} (hr : r ≠ 0) :
    (0 : ℤ) < (a : ℤ) ^ r - (b : ℤ) ^ r := by
  have : (b : ℤ) ^ r < (a : ℤ) ^ r :=
    pow_lt_pow_left₀ (by exact_mod_cast hba) (by positivity) hr
  linarith

lemma tailDen_pos (hba : b < a) : ∀ m, 0 < tailDen a b m
  | 0 => by simp [tailDen]
  | m + 1 => by
      rw [tailDen_succ]
      exact mul_pos (tailDen_pos hba m) (pow_sub_pow_pos hba (Nat.add_one_ne_zero m))

lemma tailPartialSum_zero : tailPartialSum a b 0 = 0 := by
  simp [tailPartialSum]

lemma tailPartialSum_succ (m : ℕ) :
    tailPartialSum a b (m + 1) =
      tailPartialSum a b m + ((b : ℚ) / a) ^ (m + 1) / (1 - ((b : ℚ) / a) ^ (m + 1)) := by
  unfold tailPartialSum
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma tailTerm_eq (hba : b < a) {r : ℕ} (hr : r ≠ 0) :
    ((b : ℚ) / a) ^ r / (1 - ((b : ℚ) / a) ^ r) =
      ((b : ℤ) ^ r : ℤ) / (((a : ℤ) ^ r - (b : ℤ) ^ r : ℤ) : ℚ) := by
  have ha : (a : ℚ) ≠ 0 := by
    have : (0 : ℚ) < a := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le b) hba)
    exact this.ne'
  have hpos : (0 : ℚ) < (a : ℚ) ^ r - (b : ℚ) ^ r := by
    exact_mod_cast pow_sub_pow_pos hba hr
  have hapow : (a : ℚ) ^ r ≠ 0 := pow_ne_zero r ha
  push_cast
  rw [div_pow, one_sub_div hapow, div_div_div_cancel_right₀ hapow]

lemma tailPartialSum_eq (hba : b < a) :
    ∀ m, tailPartialSum a b m = (tailNum a b m : ℚ) / (tailDen a b m : ℚ)
  | 0 => by simp [tailPartialSum_zero, tailNum, tailDen]
  | m + 1 => by
      rw [tailPartialSum_succ, tailTerm_eq hba (Nat.add_one_ne_zero m),
        tailPartialSum_eq hba m]
      have h1 : (tailDen a b m : ℚ) ≠ 0 := by exact_mod_cast (tailDen_pos hba m).ne'
      have h2 : (((a : ℤ) ^ (m + 1) - (b : ℤ) ^ (m + 1) : ℤ) : ℚ) ≠ 0 := by
        exact_mod_cast (pow_sub_pow_pos hba (Nat.add_one_ne_zero m)).ne'
      rw [div_add_div _ _ h1 h2, tailNum_succ, tailDen_succ]
      push_cast
      ring

lemma dvd_tailNum : ∀ m, (b : ℤ) ∣ tailNum a b m
  | 0 => by simp [tailNum]
  | m + 1 => by
      rw [tailNum_succ]
      exact dvd_add (dvd_mul_of_dvd_left (dvd_tailNum m) _)
        (dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.add_one_ne_zero m)) _)

lemma isCoprime_pow_sub_pow_left (hab : Nat.Coprime a b) {r : ℕ} (hr : r ≠ 0) :
    IsCoprime ((a : ℤ) ^ r - (b : ℤ) ^ r) (a : ℤ) := by
  have hba : IsCoprime (b : ℤ) (a : ℤ) := (Nat.isCoprime_iff_coprime.mpr hab).symm
  have h := (hba.pow_left (m := r)).neg_left.add_mul_left_left ((a : ℤ) ^ (r - 1))
  have he : -(b : ℤ) ^ r + (a : ℤ) * (a : ℤ) ^ (r - 1) = (a : ℤ) ^ r - (b : ℤ) ^ r := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  rwa [he] at h

lemma isCoprime_pow_sub_pow_right (hab : Nat.Coprime a b) {r : ℕ} (hr : r ≠ 0) :
    IsCoprime ((a : ℤ) ^ r - (b : ℤ) ^ r) (b : ℤ) := by
  have hab' : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  have h := (hab'.pow_left (m := r)).add_mul_left_left (-(b : ℤ) ^ (r - 1))
  have he : (a : ℤ) ^ r + (b : ℤ) * -(b : ℤ) ^ (r - 1) = (a : ℤ) ^ r - (b : ℤ) ^ r := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  rwa [he] at h

lemma isCoprime_tailDen (hab : Nat.Coprime a b) :
    ∀ m, IsCoprime (tailDen a b m) ((a : ℤ) * b)
  | 0 => by simp only [tailDen]; exact isCoprime_one_left
  | m + 1 => by
      rw [tailDen_succ]
      refine IsCoprime.mul_left (isCoprime_tailDen hab m) ?_
      exact IsCoprime.mul_right (isCoprime_pow_sub_pow_left hab (Nat.add_one_ne_zero m))
        (isCoprime_pow_sub_pow_right hab (Nat.add_one_ne_zero m))

lemma tailQ_dvd_tailDen (hba : b < a) (m : ℕ) : tailQ a b m ∣ tailDen a b m := by
  unfold tailQ
  rw [tailPartialSum_eq hba m, ← Rat.divInt_eq_div]
  exact Rat.den_dvd _ _

lemma tailP_mul_tailDen (hba : b < a) (m : ℕ) :
    tailP a b m * tailDen a b m = tailNum a b m * tailQ a b m := by
  have hD : (tailDen a b m : ℚ) ≠ 0 := by exact_mod_cast (tailDen_pos hba m).ne'
  have h := Rat.mul_den_eq_num (tailPartialSum a b m)
  have hS := tailPartialSum_eq hba m
  have : ((tailP a b m * tailDen a b m : ℤ) : ℚ) =
      ((tailNum a b m * tailQ a b m : ℤ) : ℚ) := by
    unfold tailP tailQ
    push_cast
    rw [← h, hS]
    field_simp
  exact_mod_cast this

end

/-! ### The two local facts -/

theorem tailQ_coprime {a b : ℕ} (hba : b < a) (hab : Nat.Coprime a b) (m : ℕ) :
    IsCoprime (tailQ a b m) ((a : ℤ) * b) :=
  (isCoprime_tailDen hab m).of_isCoprime_of_dvd_left (tailQ_dvd_tailDen hba m)

theorem dvd_tailP {a b : ℕ} (hba : b < a) (hab : Nat.Coprime a b) (m : ℕ) :
    (b : ℤ) ∣ tailP a b m := by
  have hcop : IsCoprime (b : ℤ) (tailDen a b m) :=
    ((isCoprime_tailDen hab m).of_isCoprime_of_dvd_right (dvd_mul_left (b : ℤ) a)).symm
  have h : (b : ℤ) ∣ tailP a b m * tailDen a b m := by
    rw [tailP_mul_tailDen hba m]
    exact dvd_mul_of_dvd_left (dvd_tailNum m) _
  exact hcop.dvd_of_dvd_mul_right h

/-! ### The rows at `m = 0` and `m = 1` -/

lemma tailRow_zero (a b : ℕ) : tailRow a b 0 = (1, 0) := by
  simp [tailRow, tailQ, tailP, tailPartialSum_zero]

lemma tailPartialSum_one {a b : ℕ} (hba : b < a) :
    tailPartialSum a b 1 = ((b : ℤ) : ℚ) / (((a : ℤ) - b : ℤ) : ℚ) := by
  rw [tailPartialSum_eq hba 1]
  simp [tailNum, tailDen]

lemma tailRow_one {a b : ℕ} (hba : b < a) (hab : Nat.Coprime a b) :
    tailRow a b 1 = ((a : ℤ) - b, (b : ℤ)) := by
  have hpos : (0 : ℤ) < (a : ℤ) - b := by
    have : (b : ℤ) < a := by exact_mod_cast hba
    linarith
  have hcop : ((b : ℤ)).natAbs.Coprime (((a : ℤ) - b)).natAbs := by
    have h1 : ((a : ℤ) - b).natAbs = a - b := by omega
    rw [Int.natAbs_natCast, h1]
    exact (Nat.coprime_sub_self_right hba.le).mpr hab.symm
  simp only [tailRow, tailQ, tailP, tailPartialSum_one hba]
  rw [Rat.num_div_eq_of_coprime hpos hcop, Rat.den_div_eq_of_coprime hpos hcop]

/-! ### The prefix lattice -/

/-- `ℤ × bℤ`. -/
def zTimesBZ (b : ℕ) : Submodule ℤ (ℤ × ℤ) :=
  (⊤ : Submodule ℤ ℤ).prod (Submodule.span ℤ {(b : ℤ)})

lemma mem_zTimesBZ {b : ℕ} {v : ℤ × ℤ} : v ∈ zTimesBZ b ↔ (b : ℤ) ∣ v.2 := by
  simp only [zTimesBZ, Submodule.mem_prod, Submodule.mem_top, true_and,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk, smul_eq_mul, mul_comm]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk, smul_eq_mul, mul_comm]⟩

theorem tailPrefixLattice_eq {a b M : ℕ} (hba : b < a) (hab : Nat.Coprime a b)
    (hM : 2 ≤ M) : tailPrefixLattice a b M = zTimesBZ b := by
  apply le_antisymm
  · rw [tailPrefixLattice, Submodule.span_le]
    rintro _ ⟨m, -, rfl⟩
    exact mem_zTimesBZ.mpr (dvd_tailP hba hab m)
  · intro v hv
    obtain ⟨k, hk⟩ := mem_zTimesBZ.mp hv
    have h0 : tailRow a b 0 ∈ tailPrefixLattice a b M :=
      Submodule.subset_span ⟨0, by simp; omega, rfl⟩
    have h1 : tailRow a b 1 ∈ tailPrefixLattice a b M :=
      Submodule.subset_span ⟨1, by simp; omega, rfl⟩
    rw [tailRow_zero] at h0
    rw [tailRow_one hba hab] at h1
    have hv' : v = v.1 • ((1 : ℤ), (0 : ℤ)) +
        k • (((a : ℤ) - b, (b : ℤ)) - ((a : ℤ) - b) • ((1 : ℤ), (0 : ℤ))) := by
      ext
      · simp
      · simp [hk]; ring
    rw [hv']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h0)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h0)))

/-! ### Smith normal form -/

lemma zTimesBZ_toAddSubgroup (b : ℕ) :
    (zTimesBZ b).toAddSubgroup = (⊤ : AddSubgroup ℤ).prod (AddSubgroup.zmultiples (b : ℤ)) := by
  ext v
  simp only [Submodule.mem_toAddSubgroup, mem_zTimesBZ, AddSubgroup.mem_prod,
    AddSubgroup.mem_top, true_and, Int.mem_zmultiples_iff]

lemma zTimesBZ_index (b : ℕ) : (zTimesBZ b).toAddSubgroup.index = b := by
  rw [zTimesBZ_toAddSubgroup, AddSubgroup.index_prod, AddSubgroup.index_top, one_mul,
    Int.index_zmultiples, Int.natAbs_natCast]

/-- A Smith normal form of `ℤ × bℤ` with diagonal `(1, b)`. -/
lemma exists_snf_zTimesBZ {b : ℕ} (hb : b ≠ 0) (L : Submodule ℤ (ℤ × ℤ)) (hL : L = zTimesBZ b) :
    ∃ snf : Module.Basis.SmithNormalForm L (Fin 2) 2, snf.a = ![1, (b : ℤ)] := by
  subst hL
  let v : Fin 2 → ℤ × ℤ := ![((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (b : ℤ))]
  have hli : LinearIndependent ℤ v := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg Prod.fst hst
    have h2 := congrArg Prod.snd hst
    simp at h1 h2
    exact ⟨h1, by rcases h2 with h | h <;> [exact h; exact absurd h (by exact_mod_cast hb)]⟩
  have hspan : Submodule.span ℤ (Set.range v) = zTimesBZ b := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [v, mem_zTimesBZ]
    · intro x hx
      obtain ⟨k, hk⟩ := mem_zTimesBZ.mp hx
      have hx' : x = x.1 • v 0 + k • v 1 := by
        ext
        · simp [v]
        · simp [v, hk, mul_comm]
      rw [hx']
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bN : Module.Basis (Fin 2) ℤ (zTimesBZ b) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  refine ⟨⟨Module.Basis.finTwoProd ℤ, bN, Function.Embedding.refl _, ![1, (b : ℤ)], ?_⟩, rfl⟩
  intro i
  simp only [bN, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]
  fin_cases i <;> simp [v]

/-- Every Smith normal form of `ℤ × bℤ` inside `ℤ²` has two diagonal entries. -/
lemma snf_rank_zTimesBZ {b : ℕ} (hb : b ≠ 0) (L : Submodule ℤ (ℤ × ℤ)) (hL : L = zTimesBZ b)
    {n : ℕ} (snf : Module.Basis.SmithNormalForm L (Fin 2) n) : n = 2 := by
  subst hL
  have h := snf.toAddSubgroup_index_eq_ite
  rw [zTimesBZ_index] at h
  by_contra hn
  rw [if_neg (by simpa using hn)] at h
  exact hb h

/-- The Smith invariants of `ℤ × bℤ` are `1, b`: in any Smith normal form whose diagonal
satisfies the divisibility `d₁ ∣ d₂`, one has `d₁ = ±1` and `d₂ = ±b`. -/
lemma snf_invariants_zTimesBZ {b : ℕ} (L : Submodule ℤ (ℤ × ℤ)) (hL : L = zTimesBZ b)
    (snf : Module.Basis.SmithNormalForm L (Fin 2) 2) (hdvd : snf.a 0 ∣ snf.a 1) :
    IsUnit (snf.a 0) ∧ Associated (snf.a 1) (b : ℤ) := by
  subst hL
  obtain ⟨t, ht⟩ := hdvd
  -- every element of `L` is `d₁` times an integer vector
  have hmul : ∀ x ∈ zTimesBZ b, ∃ u : ℤ × ℤ, x = snf.a 0 • u := by
    intro x hx
    obtain ⟨c, rfl⟩ := (snf.bN.mem_submodule_iff' (x := x)).mp hx
    refine ⟨c 0 • snf.bM (snf.f 0) + (c 1 * t) • snf.bM (snf.f 1), ?_⟩
    rw [Fin.sum_univ_two, snf.snf, snf.snf, ht]
    simp only [smul_add, smul_smul]
    congr 1
    · rw [mul_comm]
    · ring_nf
  have hunit : IsUnit (snf.a 0) := by
    have h10 : ((1 : ℤ), (0 : ℤ)) ∈ zTimesBZ b := by
      rw [mem_zTimesBZ]
      exact dvd_zero _
    obtain ⟨u, hu⟩ := hmul _ h10
    have h1 := congrArg Prod.fst hu
    simp only [Prod.smul_fst, smul_eq_mul] at h1
    exact isUnit_of_dvd_one ⟨u.1, h1⟩
  refine ⟨hunit, ?_⟩
  have hidx := snf.toAddSubgroup_index_eq_ite
  rw [zTimesBZ_index, if_pos (by simp), Fin.prod_univ_two,
    Ideal.span_singleton_toAddSubgroup_eq_zmultiples,
    Ideal.span_singleton_toAddSubgroup_eq_zmultiples, Int.index_zmultiples,
    Int.index_zmultiples, Int.isUnit_iff_natAbs_eq.mp hunit, one_mul] at hidx
  rw [Int.associated_iff_natAbs, Int.natAbs_natCast]
  exact hidx.symm

/-! ### Minors -/

lemma tailMinor_zero_one {a b : ℕ} (hba : b < a) (hab : Nat.Coprime a b) :
    tailMinor a b 0 1 = b := by
  have h0 := tailRow_zero a b
  have h1 := tailRow_one hba hab
  simp only [tailRow, Prod.mk.injEq] at h0 h1
  simp [tailMinor, h0.1, h0.2, h1.1, h1.2]

lemma dvd_tailMinor {a b : ℕ} (hba : b < a) (hab : Nat.Coprime a b) (i j : ℕ) :
    (b : ℤ) ∣ tailMinor a b i j := by
  unfold tailMinor
  exact dvd_sub (dvd_mul_of_dvd_right (dvd_tailP hba hab j) _)
    (dvd_mul_of_dvd_left (dvd_tailP hba hab i) _)

/-! ### Reduction modulo `D` -/

lemma image_rowModD_zTimesBZ (b D : ℕ) [NeZero D] :
    rowModD D '' (zTimesBZ b : Set (ℤ × ℤ)) =
      (Set.univ : Set (ZMod D)) ×ˢ (AddSubgroup.zmultiples ((b : ℕ) : ZMod D) : Set (ZMod D)) := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, SetLike.mem_coe, mem_zTimesBZ, rowModD, Set.mem_prod,
    Set.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨v, ⟨k, hk⟩, -, rfl⟩
    rw [hk, AddSubgroup.mem_zmultiples_iff]
    exact ⟨k, by push_cast; rw [zsmul_eq_mul, mul_comm]⟩
  · intro hy
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    refine ⟨((x.val : ℤ), (b : ℤ) * k), ⟨k, rfl⟩, ?_, ?_⟩
    · simp
    · push_cast; rw [zsmul_eq_mul, mul_comm]

lemma ncard_image_rowModD_zTimesBZ (b D : ℕ) (hD : 1 ≤ D) :
    (rowModD D '' (zTimesBZ b : Set (ℤ × ℤ))).ncard = D ^ 2 / Nat.gcd b D := by
  haveI : NeZero D := ⟨by omega⟩
  rw [image_rowModD_zTimesBZ, Set.ncard_prod, Set.ncard_univ, Nat.card_zmod,
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_zmultiples,
    ZMod.addOrderOf_coe _ (by omega), Nat.gcd_comm D b, sq,
    Nat.mul_div_assoc _ (Nat.gcd_dvd_right b D)]

/-! ### Rational weights -/

/-- The rational line through a primitive integer pair meets `ℤ²` exactly in the integer
multiples of that pair. -/
lemma int_multiple_of_rat_multiple {Q P : ℤ} (hQP : Int.gcd Q P = 1) {μ : ℚ}
    {A B : ℤ} (hA : (A : ℚ) = μ * Q) (hB : (B : ℚ) = μ * P) :
    ∃ k : ℤ, (k : ℚ) = μ ∧ A = k * Q ∧ B = k * P := by
  have hden : μ.den = 1 := by
    have hmd := Rat.mul_den_eq_num μ
    have eA : A * (μ.den : ℤ) = μ.num * Q := by
      have : (A : ℚ) * μ.den = μ.num * Q := by
        rw [hA, mul_right_comm, hmd]
      exact_mod_cast this
    have eB : B * (μ.den : ℤ) = μ.num * P := by
      have : (B : ℚ) * μ.den = μ.num * P := by
        rw [hB, mul_right_comm, hmd]
      exact_mod_cast this
    have hcop : IsCoprime (μ.den : ℤ) μ.num := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      simpa [Int.gcd, Int.natAbs_natCast] using μ.reduced
    have hdQ : (μ.den : ℤ) ∣ Q := hcop.dvd_of_dvd_mul_left ⟨A, by rw [← eA]; ring⟩
    have hdP : (μ.den : ℤ) ∣ P := hcop.dvd_of_dvd_mul_left ⟨B, by rw [← eB]; ring⟩
    have h1 : μ.den ∣ Int.gcd Q P := Int.dvd_gcd hdQ hdP
    rw [hQP] at h1
    exact Nat.dvd_one.mp h1
  have hk : ((μ.num : ℤ) : ℚ) = μ := Rat.coe_int_num_of_den_eq_one hden
  refine ⟨μ.num, hk, ?_, ?_⟩
  · have : (A : ℚ) = ((μ.num * Q : ℤ) : ℚ) := by
      push_cast; rw [hk, hA]
    exact_mod_cast this
  · have : (B : ℚ) = ((μ.num * P : ℤ) : ℚ) := by
      push_cast; rw [hk, hB]
    exact_mod_cast this

/-- Dividing a nonzero integer multiple of a primitive pair by its coordinate gcd returns
the pair up to sign. -/
lemma primitive_normalisation {Q P k : ℤ} (hQP : Int.gcd Q P = 1) (hk : k ≠ 0) :
    ((k * Q) / (Int.gcd (k * Q) (k * P) : ℤ), (k * P) / (Int.gcd (k * Q) (k * P) : ℤ)) = (Q, P) ∨
    ((k * Q) / (Int.gcd (k * Q) (k * P) : ℤ), (k * P) / (Int.gcd (k * Q) (k * P) : ℤ)) =
      -(Q, P) := by
  rw [Int.gcd_mul_left, hQP, mul_one]
  have hn : (k.natAbs : ℤ) ≠ 0 := by exact_mod_cast Int.natAbs_ne_zero.mpr hk
  rcases Int.natAbs_eq k with h | h
  · left
    generalize k.natAbs = n at h hn
    subst h
    rw [Int.mul_ediv_cancel_left _ hn, Int.mul_ediv_cancel_left _ hn]
  · right
    generalize k.natAbs = n at h hn
    subst h
    have e1 : -(n : ℤ) * Q = (n : ℤ) * (-Q) := by ring
    have e2 : -(n : ℤ) * P = (n : ℤ) * (-P) := by ring
    rw [e1, e2, Int.mul_ediv_cancel_left _ hn, Int.mul_ediv_cancel_left _ hn]
    rfl

theorem tailRow_primitive {a b : ℕ} (m : ℕ) : Int.gcd (tailQ a b m) (tailP a b m) = 1 := by
  unfold tailQ tailP
  rw [Int.gcd_comm]
  simpa [Int.gcd, Int.natAbs_natCast] using (tailPartialSum a b m).reduced

/-! ### The proposition -/

/-- `long1049:res:tail-lattice`: the prefix lattice of the tails.

Let `a > b ≥ 1` be coprime and write `S_m(b/a) = ∑_{r ≤ m} (b/a)^r / (1 - (b/a)^r)` in lowest
terms as `P_m / Q_m` with `Q_m > 0` (so `P_0 = 0`, `Q_0 = 1`).  Then:

* `(Q_m, P_m)` is a primitive integer row with `Q_m > 0`;
* every `Q_m` is coprime to `ab`, and `b` divides every `P_m`;
* for every prefix containing `m = 0` and `m = 1`, i.e. every `M ≥ 2`,
  `span_ℤ {(Q_m, P_m) : 0 ≤ m < M} = ℤ × bℤ`;
* so the Smith invariants are `1, b`: a Smith normal form with diagonal `(1, b)` exists,
  every Smith normal form of this lattice in `ℤ²` has exactly two diagonal entries, and any
  Smith normal form with `d₁ ∣ d₂` has `d₁ = ±1` and `d₂ = ±b`;
* the gcd of the `2 × 2` minors `Q_i P_j - P_i Q_j` (`i, j < M`) is `b`;
* for every `D ≥ 1` the image modulo `D` has cardinality `D² / gcd(b, D)`;
* multiplying an individual tail by a nonzero rational weight `w` leaves its primitive row
  unchanged up to sign: if clearing denominators in `w • (Q_m, P_m)` by any nonzero rational
  factor `c` gives the integer row `(A, B)`, then `(A, B)` is a nonzero integer multiple of
  `(Q_m, P_m)`, and dividing `(A, B)` by its coordinate gcd returns `±(Q_m, P_m)`.  (The tail
  `w (F(a/b) - S_m)` has row `(w / Q_m) • (Q_m, P_m)`, which is covered by taking the weight
  `w / Q_m`.) -/
theorem tail_prefix_lattice (a b : ℕ) (hb : 1 ≤ b) (hba : b < a) (hab : Nat.Coprime a b) :
    (∀ m, 0 < tailQ a b m ∧ Int.gcd (tailQ a b m) (tailP a b m) = 1) ∧
    (∀ m, IsCoprime (tailQ a b m) ((a : ℤ) * b)) ∧
    (∀ m, (b : ℤ) ∣ tailP a b m) ∧
    (∀ M, 2 ≤ M →
      tailPrefixLattice a b M = (⊤ : Submodule ℤ ℤ).prod (Submodule.span ℤ {(b : ℤ)}) ∧
      (∃ snf : Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) 2,
          snf.a = ![1, (b : ℤ)]) ∧
      (∀ n, Nonempty (Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) n) → n = 2) ∧
      (∀ snf : Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) 2,
          snf.a 0 ∣ snf.a 1 → IsUnit (snf.a 0) ∧ Associated (snf.a 1) (b : ℤ)) ∧
      (Finset.univ : Finset (Fin M × Fin M)).gcd
          (fun ij => tailMinor a b ij.1 ij.2) = (b : ℤ) ∧
      (∀ D : ℕ, 1 ≤ D →
        (rowModD D '' (tailPrefixLattice a b M : Set (ℤ × ℤ))).ncard = D ^ 2 / Nat.gcd b D)) ∧
    (∀ m (w : ℚ), w ≠ 0 → ∀ (c : ℚ) (A B : ℤ), c ≠ 0 →
      (A : ℚ) = c * (w * tailQ a b m) → (B : ℚ) = c * (w * tailP a b m) →
      (∃ k : ℤ, k ≠ 0 ∧ (A, B) = k • tailRow a b m) ∧
      ((A / (Int.gcd A B : ℤ), B / (Int.gcd A B : ℤ)) = tailRow a b m ∨
        (A / (Int.gcd A B : ℤ), B / (Int.gcd A B : ℤ)) = -tailRow a b m)) := by
  have hb0 : b ≠ 0 := by omega
  refine ⟨fun m => ⟨by unfold tailQ; exact_mod_cast (tailPartialSum a b m).den_pos,
    tailRow_primitive m⟩, tailQ_coprime hba hab, dvd_tailP hba hab, ?_, ?_⟩
  · intro M hM
    have hL := tailPrefixLattice_eq hba hab hM
    refine ⟨hL, exists_snf_zTimesBZ hb0 _ hL, fun n ⟨snf⟩ => snf_rank_zTimesBZ hb0 _ hL snf,
      fun snf hdvd => snf_invariants_zTimesBZ _ hL snf hdvd, ?_, ?_⟩
    · -- the gcd of the minors
      have hM0 : 0 < M := by omega
      have hM1 : 1 < M := by omega
      apply Int.dvd_antisymm
      · exact Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
      · exact Int.natCast_nonneg b
      · have := Finset.gcd_dvd (s := (Finset.univ : Finset (Fin M × Fin M)))
          (f := fun ij => tailMinor a b ij.1 ij.2) (b := (⟨0, hM0⟩, ⟨1, hM1⟩)) (Finset.mem_univ _)
        simpa [tailMinor_zero_one hba hab] using this
      · exact Finset.dvd_gcd_iff.mpr fun ij _ => dvd_tailMinor hba hab _ _
    · intro D hD
      rw [hL]
      exact ncard_image_rowModD_zTimesBZ b D hD
  · intro m w hw c A B hc hA hB
    have hQP := tailRow_primitive (a := a) (b := b) m
    obtain ⟨k, hkμ, hkA, hkB⟩ := int_multiple_of_rat_multiple hQP
      (μ := c * w) (by rw [hA]; ring) (by rw [hB]; ring)
    have hk : k ≠ 0 := by
      intro h
      rw [h, Int.cast_zero] at hkμ
      exact mul_ne_zero hc hw hkμ.symm
    refine ⟨⟨k, hk, ?_⟩, ?_⟩
    · simp [tailRow, hkA, hkB]
    · subst hkA hkB
      exact primitive_normalisation hQP hk

end ErdosProblems.Erdos1049.PaperCompleteR21.TailLattice

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.TailLattice.tail_prefix_lattice
