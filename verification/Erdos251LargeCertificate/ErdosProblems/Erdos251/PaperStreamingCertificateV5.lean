import ErdosProblems.Erdos251.KernelDenominatorFloor

/-!
# Restartable streaming prime certificate

UNRUN proof-source candidate.  Unlike primeSumLoop, the integer prefix is
accumulated by Horner's rule: A <- 2*A+p when a prime is encountered.
Fixed-size blocks can be compiled separately and their endpoint equalities
chained.  Generated endpoint literals are not trusted: each block must
succeed with `decide +kernel`.  Neither native_decide nor an external
primality oracle is used.  This is a scheduling/representation repair, not
a claim of measured compilation performance.
-/

open scoped BigOperators
open Finset
namespace ErdosProblems.Erdos251.PaperV5.Streaming

noncomputable def primeHorner : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * primeHorner n + prime0 n

/-- Semantic identity, independent of any enumeration implementation. -/
theorem primeHorner_prefix (n : ℕ) :
    (∑ i ∈ range n, primeDyadicTerm i) = (primeHorner n : ℝ) / 2 ^ n := by
  induction n with
  | zero => simp [primeHorner]
  | succ n ih =>
      rw [sum_range_succ, ih, primeHorner]
      push_cast
      unfold primeDyadicTerm
      rw [pow_succ]
      field_simp
      <;> ring

def step (m : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  if isPrimeTD m then (s.1 + 1, 2 * s.2 + m) else s

def primePrefix : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 => step m (primePrefix m)

/- Keep the generated checkpoint vocabulary source-compatible after `prefix`
became reserved syntax in Lean 4.29. -/
syntax "prefix" term:max : term
macro_rules
  | `(prefix $X) => `(primePrefix $X)

/-- Both coordinates are proved; no supplied list of primes is assumed. -/
theorem prefix_semantics (X : ℕ) :
    primePrefix X = (Nat.count Nat.Prime X, primeHorner (Nat.count Nat.Prime X)) := by
  induction X with
  | zero => simp [primePrefix, primeHorner]
  | succ X ih =>
      by_cases hp : Nat.Prime X
      · have hb : isPrimeTD X = true := (isPrimeTD_eq_true_iff X).2 hp
        have hnth : prime0 (Nat.count Nat.Prime X) = X := Nat.nth_count hp
        simp [primePrefix, step, hb, ih, Nat.count_succ, hp, primeHorner, hnth]
      · have hb : isPrimeTD X = false := by
          rw [← Bool.not_eq_true, isPrimeTD_eq_true_iff]
          exact hp
        simp [primePrefix, step, hb, ih, Nat.count_succ, hp]

def scanBlock (start length : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  match length with
  | 0 => s
  | length + 1 => scanBlock (start + 1) length (step start s)
termination_by length

/-- Composition rule which makes every finite block independently replayable. -/
theorem scanBlock_prefix (start length : ℕ) :
    scanBlock start length (primePrefix start) = primePrefix (start + length) := by
  induction length generalizing start with
  | zero => simp [scanBlock]
  | succ length ih =>
      rw [scanBlock]
      have hs : step start (primePrefix start) = primePrefix (start + 1) := by
        rw [show start + 1 = Nat.succ start by omega]
        rfl
      rw [hs, ih]
      congr 1
      omega

/-- A streaming endpoint gives exactly the real finite prefix used in the
infinite tail enclosure.  No claim about a floating-point sum appears. -/
theorem finite_prefix_of_endpoint (X c A : ℕ) (h : primePrefix X = (c, A)) :
    (∑ i ∈ range c, primeDyadicTerm i) = (A : ℝ) / 2 ^ c := by
  have hs := prefix_semantics X
  have hc : Nat.count Nat.Prime X = c := by
    have he := congrArg Prod.fst (hs.symm.trans h)
    exact he
  have hA : primeHorner c = A := by
    have he := congrArg Prod.snd (hs.symm.trans h)
    simpa only [hc] using he
  rw [primeHorner_prefix, hA]

/-- Farey separation with an independently verified streaming endpoint.
The old monolithic certificate is NOT imported as a proof dependency. -/
theorem denominator_bound (X c A u v up vp : ℕ)
    (hc : 9 ≤ c) (hprefix : primePrefix X = (c, A))
    (hv : 0 < v) (hvp : 0 < vp) (hdet : up * v = u * vp + 1)
    (hlo : u * 2 ^ c < A * v)
    (hhi : (2 * A + 5000 * (c + 1) ^ 4) * vp < up * 2 ^ (c + 1))
    (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b) : v + vp ≤ b := by
  have hfinite := finite_prefix_of_endpoint X c A hprefix
  obtain ⟨hb1, hb2⟩ := tsum_primeDyadicTerm_bracket c hc
  rw [hfinite] at hb1 hb2
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  have h2c1 : (0 : ℝ) < 2 ^ (c + 1) := by positivity
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvpR : (0 : ℝ) < vp := by exact_mod_cast hvp
  have hleft : (u : ℝ) / v < (A : ℝ) / 2 ^ c := by
    rw [div_lt_div_iff₀ hvR h2c]
    exact_mod_cast hlo
  have hright : ((2 * A + 5000 * (c + 1) ^ 4 : ℕ) : ℝ) / 2 ^ (c + 1) <
      (up : ℝ) / vp := by
    rw [div_lt_div_iff₀ h2c1 hvpR]
    exact_mod_cast hhi
  have hsum : (A : ℝ) / 2 ^ c + 5000 * (c + 1) ^ 4 / 2 ^ (c + 1) =
      ((2 * A + 5000 * (c + 1) ^ 4 : ℕ) : ℝ) / 2 ^ (c + 1) := by
    push_cast
    rw [pow_succ]
    field_simp
    <;> ring
  refine den_ge_of_between u v up vp hv hvp hdet a b hb ?_ ?_
  · rw [← hS]
    exact lt_of_lt_of_le hleft hb1
  · rw [← hS]
    exact lt_of_le_of_lt hb2 (by rw [hsum]; exact hright)

end ErdosProblems.Erdos251.PaperV5.Streaming
