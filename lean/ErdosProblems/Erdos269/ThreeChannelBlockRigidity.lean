import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
# Erdős #269: signed three-channel block rigidity

If every block between two occurrences of the same channel has signed sum
zero, then the signed word is a coboundary of a potential on the channel
space.  For three channels, zero perturbation at transitions `2 → 3` and
`2 → 5` makes that potential constant and therefore makes the entire signed
word zero.

No declaration here asserts irrationality of the `{2,3,5}` running-LCM
series.  In particular, the file neither constructs the ordered-power jump
word nor proves that its induced perturbation is block-null.  Those are
separate problem-specific inputs.
-/

namespace ErdosProblems.Erdos269

open scoped BigOperators

/-- Prefix sum before index `N`.  The zero-based convention makes a block
`[a,b)` equal to the difference of the prefixes at `b` and `a`. -/
def channelPrefix {G : Type*} [AddCommGroup G]
    (ε : ℕ → G) (N : ℕ) : G :=
  ∑ n ∈ Finset.range N, ε n

/-- Every two boundaries carrying the same channel have the same prefix.
This is the boundary form of saying that every complete channel block has
signed sum zero. -/
def ChannelBlockNull {ι G : Type*} [AddCommGroup G]
    (jumpBase : ℕ → ι) (ε : ℕ → G) : Prop :=
  ∀ a b, jumpBase a = jumpBase b →
    channelPrefix ε a = channelPrefix ε b

theorem channelPrefix_succ {G : Type*} [AddCommGroup G]
    (ε : ℕ → G) (N : ℕ) :
    channelPrefix ε (N + 1) = channelPrefix ε N + ε N := by
  simp [channelPrefix, Finset.sum_range_succ]

/-- A channel potential telescopes exactly along the jump word. -/
theorem sum_range_channelCoboundary {ι G : Type*} [AddCommGroup G]
    (jumpBase : ℕ → ι) (C : ι → G) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        (C (jumpBase (n + 1)) - C (jumpBase n)) =
      C (jumpBase N) - C (jumpBase 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      abel

/-- If every channel occurs and all complete same-channel blocks have zero
signed sum, then the word is exactly a channel coboundary.  Conversely every
channel coboundary has zero sum on such blocks.  The surjectivity hypothesis
is an explicit assumption; this theorem does not construct a channel word. -/
theorem channelBlockNull_iff_channelPotential
    {ι G : Type*} [AddCommGroup G]
    (jumpBase : ℕ → ι) (ε : ℕ → G)
    (hbase : Function.Surjective jumpBase) :
    ChannelBlockNull jumpBase ε ↔
      ∃ C : ι → G, ∀ N,
        ε N = C (jumpBase (N + 1)) - C (jumpBase N) := by
  constructor
  · intro hnull
    classical
    choose representative hrepresentative using hbase
    let C : ι → G := fun i => channelPrefix ε (representative i)
    refine ⟨C, ?_⟩
    intro N
    have hleft : C (jumpBase N) = channelPrefix ε N := by
      apply hnull
      simpa [C] using hrepresentative (jumpBase N)
    have hright : C (jumpBase (N + 1)) = channelPrefix ε (N + 1) := by
      apply hnull
      simpa [C] using hrepresentative (jumpBase (N + 1))
    rw [hright, hleft, channelPrefix_succ]
    abel
  · rintro ⟨C, hpotential⟩
    intro a b hab
    have hprefix : ∀ N,
        channelPrefix ε N = C (jumpBase N) - C (jumpBase 0) := by
      intro N
      rw [channelPrefix]
      simpa only [hpotential] using
        sum_range_channelCoboundary jumpBase C N
    rw [hprefix a, hprefix b, hab]

/-- The three channels relevant to the first unresolved case of Erdős #269. -/
inductive Prime235
  | two
  | three
  | five
  deriving DecidableEq

/-- Two zero perturbations at transitions `2 → 3` and `2 → 5` identify all
three potential values.  The resulting channel coboundary is therefore zero
at every index. -/
theorem channelCoboundary_eq_zero_of_two_anchors
    {G : Type*} [AddCommGroup G]
    {jumpBase : ℕ → Prime235} {ε : ℕ → G} {C : Prime235 → G}
    (hpotential : ∀ N,
      ε N = C (jumpBase (N + 1)) - C (jumpBase N))
    {n23 n25 : ℕ}
    (h23start : jumpBase n23 = .two)
    (h23end : jumpBase (n23 + 1) = .three)
    (h25start : jumpBase n25 = .two)
    (h25end : jumpBase (n25 + 1) = .five)
    (hanchor23 : ε n23 = 0)
    (hanchor25 : ε n25 = 0) :
    ∀ N, ε N = 0 := by
  have hCthree : C .three = C .two := by
    have h := hpotential n23
    rw [h23start, h23end, hanchor23] at h
    exact sub_eq_zero.mp h.symm
  have hCfive : C .five = C .two := by
    have h := hpotential n25
    rw [h25start, h25end, hanchor25] at h
    exact sub_eq_zero.mp h.symm
  intro N
  rw [hpotential]
  cases hstart : jumpBase N <;>
    cases hend : jumpBase (N + 1) <;>
    simp [hCthree, hCfive]

end ErdosProblems.Erdos269
