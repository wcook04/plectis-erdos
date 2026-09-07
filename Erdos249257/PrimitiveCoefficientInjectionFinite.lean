import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.GCD.Basic

/-!
# Finite part of the primitive coefficient injection

The ordinary proof of `c_(2,11)(N) ≥ c_(10,11)(N)` reduces one case to

`U (5 * m) ≥ U m` for `m ≤ 1218` and `5 ∤ m`,

where `U m` counts reduced residues in `(m / 2, 6m / 11)`. The analytic
estimate in the accompanying note proves the inequality above this range.
This file certifies exactly the finite residue count used there.

The certificate is kernel-reduced, not compiler-evaluated, so the exported
theorem carries no `Lean.ofReduceBool`. Three shapes make that practical.
Deciding the quantified statement directly forces the kernel to materialise
a filtered `Finset.range` for each of the 1219 ranks, so `primitive211Count`
is the same count written as an accumulating recursion that stays inside
`Nat`; kernel reduction then performs only `Nat` comparisons, `Nat.gcd`
calls, and additions, all of which the kernel evaluates with its accelerated
`Nat` operations. Both recursions go through `Nat.rec` directly rather than
the equation compiler, whose course-of-values tower would be rebuilt at
depth `5 * m` for every rank. And the run is cut into twenty blocks, each
kernel-decided in its own declaration, so no single kernel typecheck has to
hold the whole reduction trace; the blocks shorten as the rank grows because
the per-rank cost grows with the rank.

`primitive211Count_eq` proves the accumulating form is the `Finset` count and
`primitive211ScaleFiveRange_spec` proves a block certificate implies the
inequality on its own ranks, so nothing about the exported statement changes.
-/

namespace Erdos249257

/-- Reduced residues in the open interval `(n/2, 6n/11)`. -/
def primitive211IntervalCount (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k =>
    2 * k > n ∧ 11 * k < 6 * n ∧ Nat.Coprime k n).card

/-- Boolean membership test for a single residue `k` at modulus `n`. -/
def primitive211Mem (n k : ℕ) : Bool :=
  decide (2 * k > n ∧ 11 * k < 6 * n ∧ Nat.Coprime k n)

/-- Accumulating count of the residues below `b` that pass
`primitive211Mem n`.  Written with `Nat.rec` directly rather than through
the equation compiler: the course-of-values tower the compiler emits would
be rebuilt at depth `5 * m` for every rank and is what drives kernel memory
into the gigabytes, while this form keeps the recursive call in tail
position and the working set flat. -/
def primitive211Count (n b acc : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun a => a)
    (fun k ih a => ih (a + (primitive211Mem n k).toNat)) b acc

theorem primitive211Count_zero (n acc : ℕ) :
    primitive211Count n 0 acc = acc := rfl

theorem primitive211Count_succ (n b acc : ℕ) :
    primitive211Count n (b + 1) acc =
      primitive211Count n b (acc + (primitive211Mem n b).toNat) := rfl

/-- The accumulating count is the filtered-range cardinality. -/
theorem primitive211Count_eq (n : ℕ) :
    ∀ b acc : ℕ,
      primitive211Count n b acc =
        acc + ((Finset.range b).filter fun k =>
          2 * k > n ∧ 11 * k < 6 * n ∧ Nat.Coprime k n).card := by
  intro b
  induction b with
  | zero => intro acc; simp [primitive211Count_zero]
  | succ b ih =>
      intro acc
      rw [primitive211Count_succ, ih, Finset.range_add_one, Finset.filter_insert]
      by_cases h : 2 * b > n ∧ 11 * b < 6 * n ∧ Nat.Coprime b n
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
        simp only [primitive211Mem, decide_eq_true h, Bool.toNat_true]
        omega
      · rw [if_neg h]
        simp only [primitive211Mem, decide_eq_false h, Bool.toNat_false]
        omega

/-- The exported interval count in accumulating form. -/
theorem primitive211IntervalCount_eq (n : ℕ) :
    primitive211IntervalCount n = primitive211Count n n 0 := by
  rw [primitive211Count_eq, Nat.zero_add, primitive211IntervalCount]

/-- One rank of the scale-five check. -/
def primitive211ScaleFiveStep (m : ℕ) : Bool :=
  (m + 1) % 5 == 0 ||
    Nat.ble (primitive211Count (m + 1) (m + 1) 0)
      (primitive211Count (5 * (m + 1)) (5 * (m + 1)) 0)

/-- Boolean certificate for the `len` ranks `lo + 1, …, lo + len`. -/
def primitive211ScaleFiveRange (lo len : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => primitive211ScaleFiveStep (lo + j) && ih) len

theorem primitive211ScaleFiveRange_succ (lo len : ℕ) :
    primitive211ScaleFiveRange lo (len + 1) =
      (primitive211ScaleFiveStep (lo + len) &&
        primitive211ScaleFiveRange lo len) := rfl

/-- The block certificate implies the inequality on its own ranks. -/
theorem primitive211ScaleFiveRange_spec (lo : ℕ) :
    ∀ len : ℕ, primitive211ScaleFiveRange lo len = true →
      ∀ m : ℕ, lo < m → m ≤ lo + len → m % 5 ≠ 0 →
        primitive211IntervalCount m ≤ primitive211IntervalCount (5 * m) := by
  intro len
  induction len with
  | zero => intro _ m hlo hle _; omega
  | succ len ih =>
      intro hcert m hlo hle h5
      rw [primitive211ScaleFiveRange_succ, Bool.and_eq_true] at hcert
      obtain ⟨hhead, htail⟩ := hcert
      by_cases hm : m = lo + len + 1
      · subst hm
        rw [primitive211ScaleFiveStep, Bool.or_eq_true] at hhead
        rcases hhead with h0 | hble
        · exact absurd (by simpa using h0) h5
        · rw [primitive211IntervalCount_eq (lo + len + 1),
            primitive211IntervalCount_eq (5 * (lo + len + 1))]
          exact Nat.le_of_ble_eq_true hble
      · exact ih htail m hlo (by omega) h5

/-- The scale-five inequality certified for every rank up to `N`. -/
def PrimitiveScaleFiveCertified (N : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ N → m % 5 ≠ 0 →
    primitive211IntervalCount m ≤ primitive211IntervalCount (5 * m)

theorem primitiveScaleFiveCertified_zero : PrimitiveScaleFiveCertified 0 := by
  intro m h1 hm _
  omega

/-- Extend a certified prefix by one kernel-decided block. -/
theorem primitiveScaleFiveCertified_step {lo len : ℕ}
    (h : PrimitiveScaleFiveCertified lo)
    (hc : primitive211ScaleFiveRange lo len = true) :
    PrimitiveScaleFiveCertified (lo + len) := by
  intro m h1 hm h5
  by_cases hlo : m ≤ lo
  · exact h m h1 hlo h5
  · exact primitive211ScaleFiveRange_spec lo len hc m (by omega) (by omega) h5

/-! ### Kernel-decided blocks

The blocks are sized so each carries roughly the same amount of kernel
reduction, which is why they get shorter as the rank grows. -/

theorem primitive211ScaleFiveRange_0_272 :
    primitive211ScaleFiveRange 0 272 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_272 : PrimitiveScaleFiveCertified 272 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_zero primitive211ScaleFiveRange_0_272

theorem primitive211ScaleFiveRange_272_113 :
    primitive211ScaleFiveRange 272 113 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_385 : PrimitiveScaleFiveCertified 385 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_272 primitive211ScaleFiveRange_272_113

theorem primitive211ScaleFiveRange_385_87 :
    primitive211ScaleFiveRange 385 87 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_472 : PrimitiveScaleFiveCertified 472 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_385 primitive211ScaleFiveRange_385_87

theorem primitive211ScaleFiveRange_472_73 :
    primitive211ScaleFiveRange 472 73 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_545 : PrimitiveScaleFiveCertified 545 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_472 primitive211ScaleFiveRange_472_73

theorem primitive211ScaleFiveRange_545_64 :
    primitive211ScaleFiveRange 545 64 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_609 : PrimitiveScaleFiveCertified 609 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_545 primitive211ScaleFiveRange_545_64

theorem primitive211ScaleFiveRange_609_58 :
    primitive211ScaleFiveRange 609 58 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_667 : PrimitiveScaleFiveCertified 667 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_609 primitive211ScaleFiveRange_609_58

theorem primitive211ScaleFiveRange_667_54 :
    primitive211ScaleFiveRange 667 54 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_721 : PrimitiveScaleFiveCertified 721 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_667 primitive211ScaleFiveRange_667_54

theorem primitive211ScaleFiveRange_721_49 :
    primitive211ScaleFiveRange 721 49 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_770 : PrimitiveScaleFiveCertified 770 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_721 primitive211ScaleFiveRange_721_49

theorem primitive211ScaleFiveRange_770_47 :
    primitive211ScaleFiveRange 770 47 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_817 : PrimitiveScaleFiveCertified 817 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_770 primitive211ScaleFiveRange_770_47

theorem primitive211ScaleFiveRange_817_44 :
    primitive211ScaleFiveRange 817 44 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_861 : PrimitiveScaleFiveCertified 861 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_817 primitive211ScaleFiveRange_817_44

theorem primitive211ScaleFiveRange_861_42 :
    primitive211ScaleFiveRange 861 42 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_903 : PrimitiveScaleFiveCertified 903 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_861 primitive211ScaleFiveRange_861_42

theorem primitive211ScaleFiveRange_903_40 :
    primitive211ScaleFiveRange 903 40 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_943 : PrimitiveScaleFiveCertified 943 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_903 primitive211ScaleFiveRange_903_40

theorem primitive211ScaleFiveRange_943_39 :
    primitive211ScaleFiveRange 943 39 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_982 : PrimitiveScaleFiveCertified 982 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_943 primitive211ScaleFiveRange_943_39

theorem primitive211ScaleFiveRange_982_37 :
    primitive211ScaleFiveRange 982 37 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_1019 : PrimitiveScaleFiveCertified 1019 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_982 primitive211ScaleFiveRange_982_37

theorem primitive211ScaleFiveRange_1019_36 :
    primitive211ScaleFiveRange 1019 36 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_1055 : PrimitiveScaleFiveCertified 1055 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_1019 primitive211ScaleFiveRange_1019_36

theorem primitive211ScaleFiveRange_1055_34 :
    primitive211ScaleFiveRange 1055 34 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_1089 : PrimitiveScaleFiveCertified 1089 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_1055 primitive211ScaleFiveRange_1055_34

theorem primitive211ScaleFiveRange_1089_34 :
    primitive211ScaleFiveRange 1089 34 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_1123 : PrimitiveScaleFiveCertified 1123 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_1089 primitive211ScaleFiveRange_1089_34

theorem primitive211ScaleFiveRange_1123_32 :
    primitive211ScaleFiveRange 1123 32 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_1155 : PrimitiveScaleFiveCertified 1155 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_1123 primitive211ScaleFiveRange_1123_32

theorem primitive211ScaleFiveRange_1155_32 :
    primitive211ScaleFiveRange 1155 32 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_1187 : PrimitiveScaleFiveCertified 1187 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_1155 primitive211ScaleFiveRange_1155_32

theorem primitive211ScaleFiveRange_1187_31 :
    primitive211ScaleFiveRange 1187 31 = true := by
  decide +kernel

theorem primitiveScaleFiveCertified_1218 : PrimitiveScaleFiveCertified 1218 :=
  primitiveScaleFiveCertified_step primitiveScaleFiveCertified_1187 primitive211ScaleFiveRange_1187_31

/-- The finite part of the scale-five inequality. -/
theorem primitive211IntervalCount_scale_five_small :
    ∀ m ∈ Finset.range 1219,
      1 ≤ m → m % 5 ≠ 0 →
        primitive211IntervalCount m ≤
          primitive211IntervalCount (5 * m) := by
  intro m hm h1 h5
  exact primitiveScaleFiveCertified_1218 m h1 (by have := Finset.mem_range.mp hm; omega) h5


end Erdos249257
