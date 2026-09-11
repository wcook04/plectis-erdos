import Mathlib.Data.Nat.Fib.Basic
import Erdos249257.GcdMomentCalculus

/-!
# Stern--Brocot geometry after inducing parabolic runs

This file isolates the unconditional combinatorial core of the induced-run
coordinate for the positive primitive-pair mass

`∑_{a,b ≥ 1, Nat.Coprime a b} 2^{-(a+b)}`.

The existing `GcdMomentCalculus` module uses the same mediant children for its
Mersenne cylinder mass.  Here the observable is different: the height of the
literal primitive pair.  A word is stored newest run first, so its head acts
last.  This convention makes the continuant recurrence structural:

`(A,B) ↦ (n*A+B,A)`.

The first theorem is the exact Fibonacci floor.  A word with `r` nonempty
alternating runs has height at least `Nat.fib (r+3)`, with equality when every
run has length one.  The defect-sensitivity layer then expands the complete
positive continuant defect, identifies the one-site coefficient
`F_{i+2} F_{r-i+1}`, and proves the sharp global gain
`F_{r+1} * ∑ eᵢ`.  The final section records the companion arithmetic
knife-edge: the sum of the natural Fibonacci run exponents is exactly two less
than the same Fibonacci height scale.

Nothing here proves irrationality of Erdős #249.  In particular, this module
does not assert that the analytic run tail survives denominator clearing.
-/

namespace SternBrocotRunGeometry

/-! ## The literal mediant tree -/

/-- The two Stern--Brocot mediant moves. -/
inductive LR
  | left
  | right
  deriving DecidableEq, Repr

/-- Exchange the two parabolic directions. -/
def LR.flip : LR → LR
  | .left => .right
  | .right => .left

@[simp] theorem LR.flip_left : LR.left.flip = LR.right := rfl
@[simp] theorem LR.flip_right : LR.right.flip = LR.left := rfl
@[simp] theorem LR.flip_flip (d : LR) : d.flip.flip = d := by cases d <;> rfl

/-- One mediant step on a positive lattice pair. -/
def step : LR → ℕ × ℕ → ℕ × ℕ
  | .left, (a, b) => (a + b, b)
  | .right, (a, b) => (a, a + b)

/-- The pair reached from `(1,1)`.  The list head is the newest move and acts
last; this agrees with the newest-run-first convention used below. -/
def sbPair : List LR → ℕ × ℕ
  | [] => (1, 1)
  | d :: w => step d (sbPair w)

/-- Arithmetic height of a Stern--Brocot word. -/
def sbHeight (w : List LR) : ℕ := (sbPair w).1 + (sbPair w).2

/-- Every word reaches a primitive pair. -/
theorem sbPair_coprime (w : List LR) : Nat.Coprime (sbPair w).1 (sbPair w).2 := by
  induction w with
  | nil => simp [sbPair]
  | cons d w ih =>
      cases d with
      | left => simpa [sbPair, step] using Nat.coprime_add_self_left.mpr ih
      | right => simpa [sbPair, step] using Nat.coprime_add_self_right.mpr ih

/-- Both coordinates reached from `(1,1)` stay positive. -/
theorem sbPair_pos (w : List LR) : 0 < (sbPair w).1 ∧ 0 < (sbPair w).2 := by
  induction w with
  | nil => simp [sbPair]
  | cons d w ih =>
      cases d <;> simp only [sbPair, step] <;> omega

/-! ## Exact run encoding -/

/-- A word with alternating directions and the supplied run lengths.  The
first length is the newest run and its direction is `newest`. -/
def runWord : LR → List ℕ → List LR
  | _, [] => []
  | newest, n :: ns => List.replicate n newest ++ runWord newest.flip ns

/-- The direction-free continuant state at run boundaries.  Its first
coordinate is the coordinate changed by the newest run; the second is the
other coordinate. -/
def runBoundaryPair : List ℕ → ℕ × ℕ
  | [] => (1, 1)
  | n :: ns =>
      let p := runBoundaryPair ns
      (n * p.1 + p.2, p.1)

/-- Height in run coordinates. -/
def runHeight (ns : List ℕ) : ℕ :=
  (runBoundaryPair ns).1 + (runBoundaryPair ns).2

private theorem sbPair_replicate_left_append (n : ℕ) (w : List LR) :
    sbPair (List.replicate n LR.left ++ w)
      = ((sbPair w).1 + n * (sbPair w).2, (sbPair w).2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, sbPair, step, ih]
      congr 1
      ring

private theorem sbPair_replicate_right_append (n : ℕ) (w : List LR) :
    sbPair (List.replicate n LR.right ++ w)
      = ((sbPair w).1, (sbPair w).2 + n * (sbPair w).1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, sbPair, step, ih]
      congr 1
      ring

/-- The run continuant is not a new coordinate detached from the tree: it is
exactly the pair reached by the corresponding alternating Stern--Brocot word,
up to the expected coordinate swap for a newest right run. -/
theorem sbPair_runWord (newest : LR) (ns : List ℕ) :
    sbPair (runWord newest ns) =
      match newest with
      | .left => runBoundaryPair ns
      | .right => ((runBoundaryPair ns).2, (runBoundaryPair ns).1) := by
  induction ns generalizing newest with
  | nil => cases newest <;> simp [runWord, sbPair, runBoundaryPair]
  | cons n ns ih =>
      cases newest with
      | left =>
          rw [runWord, sbPair_replicate_left_append, ih]
          simp [runBoundaryPair]
          omega
      | right =>
          rw [runWord, sbPair_replicate_right_append, ih]
          simp [runBoundaryPair]
          omega

/-- Run height is the literal arithmetic height on the mediant tree. -/
theorem sbHeight_runWord (newest : LR) (ns : List ℕ) :
    sbHeight (runWord newest ns) = runHeight ns := by
  rw [sbHeight, runHeight, sbPair_runWord]
  cases newest <;> simp [Nat.add_comm]

/-- The run-boundary pair remains primitive. -/
theorem runBoundaryPair_coprime (ns : List ℕ) :
    Nat.Coprime (runBoundaryPair ns).1 (runBoundaryPair ns).2 := by
  have h := sbPair_coprime (runWord LR.left ns)
  simpa [sbPair_runWord] using h

/-! ## Fibonacci pressure -/

/-- Coordinatewise Fibonacci floor for positive run lengths. -/
theorem runBoundaryPair_fib_lower (ns : List ℕ)
    (hpos : ∀ n ∈ ns, 0 < n) :
    Nat.fib (ns.length + 2) ≤ (runBoundaryPair ns).1 ∧
      Nat.fib (ns.length + 1) ≤ (runBoundaryPair ns).2 := by
  induction ns with
  | nil => simp [runBoundaryPair]
  | cons n ns ih =>
      have hn : 0 < n := hpos n (by simp)
      have htail : ∀ m ∈ ns, 0 < m := by
        intro m hm
        exact hpos m (by simp [hm])
      obtain ⟨hfirst, hsecond⟩ := ih htail
      simp only [runBoundaryPair, List.length_cons]
      have hmul : (runBoundaryPair ns).1 ≤ n * (runBoundaryPair ns).1 :=
        Nat.le_mul_of_pos_left _ hn
      have hadd : Nat.fib (ns.length + 2) + Nat.fib (ns.length + 1) ≤
          n * (runBoundaryPair ns).1 + (runBoundaryPair ns).2 :=
        Nat.add_le_add (hfirst.trans hmul) hsecond
      constructor
      · rw [show ns.length + 1 + 2 = ns.length + 3 by omega, Nat.fib_add_two]
        change Nat.fib (ns.length + 1) + Nat.fib (ns.length + 2) ≤
          n * (runBoundaryPair ns).1 + (runBoundaryPair ns).2
        omega
      · simpa only [show ns.length + 1 + 1 = ns.length + 2 by omega] using hfirst

/-- **Fibonacci minimum height.**  Every alternating word with `r` nonempty
runs has height at least `F_{r+3}`. -/
theorem runHeight_fib_lower (ns : List ℕ)
    (hpos : ∀ n ∈ ns, 0 < n) :
    Nat.fib (ns.length + 3) ≤ runHeight ns := by
  obtain ⟨hfirst, hsecond⟩ := runBoundaryPair_fib_lower ns hpos
  unfold runHeight
  grind [Nat.fib_add_two]

/-- Tree-facing form of the Fibonacci height floor. -/
theorem sbHeight_runWord_fib_lower (newest : LR) (ns : List ℕ)
    (hpos : ∀ n ∈ ns, 0 < n) :
    Nat.fib (ns.length + 3) ≤ sbHeight (runWord newest ns) := by
  rw [sbHeight_runWord]
  exact runHeight_fib_lower ns hpos

/-- The all-unit alternating spine is exactly Fibonacci. -/
theorem runBoundaryPair_replicate_one (r : ℕ) :
    runBoundaryPair (List.replicate r 1) =
      (Nat.fib (r + 2), Nat.fib (r + 1)) := by
  induction r with
  | zero => simp [runBoundaryPair]
  | succ r ih =>
      simp only [List.replicate_succ, runBoundaryPair, ih]
      rw [show r + 1 + 2 = r + 3 by omega, show r + 1 + 1 = r + 2 by omega,
        @Nat.fib_add_two (r + 1)]
      simp only [one_mul]
      rw [show r + 1 + 1 = r + 2 by omega]
      apply Prod.ext <;> simp [Nat.add_comm]

/-- Equality case for the Fibonacci height floor. -/
theorem runHeight_replicate_one (r : ℕ) :
    runHeight (List.replicate r 1) = Nat.fib (r + 3) := by
  rw [runHeight, runBoundaryPair_replicate_one]
  grind [Nat.fib_add_two]

/-! ## Exact defect sensitivity away from the Fibonacci spine -/

/-- Replace every nonnegative defect `eᵢ` by the positive run length `1 + eᵢ`. -/
def defectRunLengths (e : List ℕ) : List ℕ :=
  e.map Nat.succ

/-- The exact defect of the two run-boundary coordinates from their Fibonacci
values.  The term `e * d.1` is the first mixed monomial created at the newest
defect; recursively expanding it gives the full positive multiaffine
continuant-defect polynomial. -/
def exactDefectPair : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | e :: es =>
      let d := exactDefectPair es
      (e * (Nat.fib (es.length + 2) + d.1) + d.1 + d.2, d.1)

/-- The degree-one part of `exactDefectPair`.  It is obtained by deleting the
mixed term `e * d.1` at every recursive step. -/
def linearDefectPair : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | e :: es =>
      let d := linearDefectPair es
      (e * Nat.fib (es.length + 2) + d.1 + d.2, d.1)

/-- Exact coordinate expansion around the all-unit Fibonacci spine. -/
theorem runBoundaryPair_defectRunLengths (e : List ℕ) :
    runBoundaryPair (defectRunLengths e) =
      (Nat.fib (e.length + 2) + (exactDefectPair e).1,
        Nat.fib (e.length + 1) + (exactDefectPair e).2) := by
  induction e with
  | nil => simp [defectRunLengths, exactDefectPair, runBoundaryPair, Nat.fib]
  | cons e es ih =>
      change runBoundaryPair (List.map Nat.succ es) = _ at ih
      simp only [defectRunLengths, List.map_cons, runBoundaryPair,
        exactDefectPair, List.length_cons]
      rw [ih]
      rw [show es.length + 1 + 2 = es.length + 3 by omega,
        show es.length + 1 + 1 = es.length + 2 by omega,
        @Nat.fib_add_two (es.length + 1)]
      apply Prod.ext <;> simp
      ring

/-- Exact height expansion.  In particular, `exactDefectPair` is not an
estimate: it owns every mixed coefficient of the continuant defect. -/
theorem runHeight_defectRunLengths (e : List ℕ) :
    runHeight (defectRunLengths e) =
      Nat.fib (e.length + 3) +
        (exactDefectPair e).1 + (exactDefectPair e).2 := by
  rw [runHeight, runBoundaryPair_defectRunLengths]
  grind [Nat.fib_add_two]

/-- Every coefficient discarded by the linearization is nonnegative. -/
theorem linearDefectPair_le_exactDefectPair (e : List ℕ) :
    (linearDefectPair e).1 ≤ (exactDefectPair e).1 ∧
      (linearDefectPair e).2 ≤ (exactDefectPair e).2 := by
  induction e with
  | nil => simp [linearDefectPair, exactDefectPair]
  | cons e es ih =>
      simp only [linearDefectPair, exactDefectPair]
      constructor
      · have hmul :
            e * Nat.fib (es.length + 2) ≤
              e * (Nat.fib (es.length + 2) + (exactDefectPair es).1) := by
            exact Nat.mul_le_mul_left e (Nat.le_add_right _ _)
        omega
      · exact ih.1

/-- Structural linear floor for the full continuant defect.  This statement
retains the recursively ordered one-site coefficients; the next theorem
identifies each of them with a closed Fibonacci product. -/
theorem runHeight_defect_linear_lower (e : List ℕ) :
    Nat.fib (e.length + 3) +
        (linearDefectPair e).1 + (linearDefectPair e).2
      ≤ runHeight (defectRunLengths e) := by
  rw [runHeight_defectRunLengths]
  obtain ⟨h1, h2⟩ := linearDefectPair_le_exactDefectPair e
  omega

/-- The recursively ordered coefficients admit the uniform sharp floor:
the first-coordinate coefficients are at least `F_r`, and the height
coefficients are at least `F_{r+1}`. -/
theorem linearDefectPair_fib_sum_lower (e : List ℕ) :
    Nat.fib e.length * e.sum ≤ (linearDefectPair e).1 ∧
      Nat.fib (e.length + 1) * e.sum ≤
        (linearDefectPair e).1 + (linearDefectPair e).2 := by
  induction e with
  | nil => simp [linearDefectPair]
  | cons e es ih =>
      simp only [linearDefectPair, List.length_cons, List.sum_cons]
      rw [show es.length + 1 + 1 = es.length + 2 by omega]
      have hmono : Nat.fib (es.length + 1) ≤ Nat.fib (es.length + 2) :=
        Nat.fib_le_fib_succ
      have hmul := Nat.mul_le_mul_left e hmono
      have hrec : Nat.fib (es.length + 2) =
          Nat.fib es.length + Nat.fib (es.length + 1) := by
        simpa [Nat.add_assoc] using (@Nat.fib_add_two es.length)
      constructor
      · nlinarith [ih.2]
      · have htail : Nat.fib (es.length + 2) * es.sum ≤
            ((linearDefectPair es).1 + (linearDefectPair es).2) +
              (linearDefectPair es).1 := by
            calc
              Nat.fib (es.length + 2) * es.sum =
                  Nat.fib es.length * es.sum +
                    Nat.fib (es.length + 1) * es.sum := by rw [hrec]; ring
              _ ≤ (linearDefectPair es).1 +
                    ((linearDefectPair es).1 + (linearDefectPair es).2) :=
                Nat.add_le_add ih.1 ih.2
              _ = ((linearDefectPair es).1 + (linearDefectPair es).2) +
                    (linearDefectPair es).1 := by omega
        calc
          Nat.fib (es.length + 2) * (e + es.sum) =
              e * Nat.fib (es.length + 2) +
                Nat.fib (es.length + 2) * es.sum := by ring
          _ ≤ e * Nat.fib (es.length + 2) +
                (((linearDefectPair es).1 + (linearDefectPair es).2) +
                  (linearDefectPair es).1) := Nat.add_le_add_left htail _
          _ = e * Nat.fib (es.length + 2) +
                (linearDefectPair es).1 + (linearDefectPair es).2 +
                  (linearDefectPair es).1 := by omega

/-- **Sharp global stability floor.**  If the positive run lengths are
`1 + eᵢ`, their height gains at least `F_{r+1}` for every unit of total
defect.  Boundary one-site rays attain this coefficient exactly. -/
theorem runHeight_defect_fib_sum_lower (e : List ℕ) :
    Nat.fib (e.length + 3) + Nat.fib (e.length + 1) * e.sum ≤
      runHeight (defectRunLengths e) := by
  have hlinear := runHeight_defect_linear_lower e
  have hweight := (linearDefectPair_fib_sum_lower e).2
  omega

/-- Closed coefficient of a defect at position `i`, counted from the newest
run boundary.  The hypothesis `i < r` keeps the coefficient inside an
`r`-run word without introducing a second indexing type. -/
def oneSiteWeight (r i : ℕ) : ℕ :=
  Nat.fib (i + 2) * Nat.fib (r - i + 1)

/-- The one-site coefficient is the boundary value `F_{r+1}` plus an
explicit interior surplus. -/
theorem oneSiteWeight_eq_base_add
    {r i : ℕ} (hi : i < r) :
    oneSiteWeight r i =
      Nat.fib (r + 1) + Nat.fib i * Nat.fib (r - i - 1) := by
  let s := r - i - 1
  have hrs : r = i + 1 + s := by omega
  rw [oneSiteWeight, hrs]
  have hidx1 : i + 1 + s - i + 1 = s + 2 := by omega
  have hidx2 : i + 1 + s - i - 1 = s := by omega
  rw [hidx1, hidx2, show i + 1 + s + 1 = i + s + 2 by omega]
  have hf := Nat.fib_add i (s + 1)
  rw [show i + (s + 1) + 1 = i + s + 2 by omega,
    show s + 1 + 1 = s + 2 by omega] at hf
  rw [hf, show i + 2 = i + 0 + 2 by omega, @Nat.fib_add_two i,
    show s + 2 = s + 0 + 2 by omega, @Nat.fib_add_two s]
  ring

/-- The recursive expansion exposes a strict mixed term as soon as the newest
defect and an older defect are both present. -/
theorem linearDefectPair_first_lt_exact_of_head_tail_pos
    {e : ℕ} (he : 0 < e) {es : List ℕ}
    (htail : 0 < (exactDefectPair es).1) :
    (linearDefectPair (e :: es)).1 < (exactDefectPair (e :: es)).1 := by
  simp only [linearDefectPair, exactDefectPair]
  have hlin := linearDefectPair_le_exactDefectPair es
  nlinarith

private theorem runHeight_one_cons (ns : List ℕ) :
    runHeight (1 :: ns) = runHeight ns + (runBoundaryPair ns).1 := by
  simp [runHeight, runBoundaryPair]

private theorem runBoundaryPair_replicate_one_append (i : ℕ) (ns : List ℕ) :
    let p := runBoundaryPair ns
    (runBoundaryPair (List.replicate i 1 ++ ns)).1 =
        Nat.fib (i + 1) * p.1 + Nat.fib i * p.2 ∧
      runHeight (List.replicate i 1 ++ ns) =
        Nat.fib (i + 2) * p.1 + Nat.fib (i + 1) * p.2 := by
  induction i with
  | zero => simp [runHeight, Nat.fib]
  | succ i ih =>
      simp only [List.replicate_succ, List.cons_append]
      have hfirst := ih.1
      have hheight := ih.2
      constructor
      · simpa [runHeight, runBoundaryPair] using hheight
      · rw [show i + 1 + 2 = i + 3 by omega, @Nat.fib_add_two (i + 1)]
        rw [show i + 1 + 1 = i + 2 by omega]
        rw [runHeight_one_cons]
        rw [hfirst, hheight]
        rw [@Nat.fib_add_two i]
        ring

/-- A single defect is exactly linear, with coefficient
`F_{i+2} F_{r-i+1}`.  This is the sharp coefficient formula and includes the
arbitrary defect magnitude `e`, not only the derivative at `e = 0`. -/
theorem runHeight_oneSiteDefect
    {r i : ℕ} (hi : i < r) (e : ℕ) :
    runHeight
        (List.replicate i 1 ++
          (e + 1) :: List.replicate (r - i - 1) 1) =
      Nat.fib (r + 3) + oneSiteWeight r i * e := by
  let s := r - i - 1
  have hrs : r = i + 1 + s := by omega
  rw [(runBoundaryPair_replicate_one_append i
    ((e + 1) :: List.replicate (r - i - 1) 1)).2]
  rw [runBoundaryPair]
  rw [runBoundaryPair_replicate_one]
  simp only [oneSiteWeight]
  rw [hrs]
  have hidx1 : i + 1 + s - i - 1 + 2 = s + 2 := by omega
  have hidx2 : i + 1 + s - i - 1 + 1 = s + 1 := by omega
  have hidx3 : i + 1 + s - i + 1 = s + 2 := by omega
  rw [hidx1, hidx2, hidx3]
  have hf := Nat.fib_add (i + 1) (s + 2)
  rw [show i + 1 + (s + 2) + 1 = i + s + 4 by omega,
    show i + 1 + 1 = i + 2 by omega,
    show s + 2 + 1 = s + 3 by omega] at hf
  rw [show i + 1 + s + 3 = i + s + 4 by omega, hf]
  rw [show s + 3 = s + 1 + 2 by omega, @Nat.fib_add_two (s + 1)]
  ring

/-- Exact height of one parabolic run. -/
@[simp] theorem runHeight_single (n : ℕ) : runHeight [n] = n + 2 := by
  simp [runHeight, runBoundaryPair]

/-- Exact height of two alternating parabolic runs.  After putting
`u = m+1`, `v = n+1`, the two orientations together contribute the weight
`2 * 2^{-(uv+1)} = 2^{-uv}` used by the second induced layer. -/
@[simp] theorem runHeight_pair (m n : ℕ) :
    runHeight [m, n] = (m + 1) * (n + 1) + 1 := by
  simp [runHeight, runBoundaryPair]
  ring

/-! ## The first two analytic run layers -/

/-- Root contribution, before any nonempty parabolic run. -/
noncomputable def zeroRunMass : ℝ :=
  ((1 : ℝ) / 2) ^ runHeight []

/-- Contribution of the two orientations with one positive run.  The natural
number index `n` represents run length `n+1`. -/
noncomputable def oneRunMass : ℝ :=
  ∑' n : ℕ, 2 * ((1 : ℝ) / 2) ^ runHeight [n + 1]

@[simp] theorem zeroRunMass_eq_quarter : zeroRunMass = 1 / 4 := by
  norm_num [zeroRunMass, runHeight, runBoundaryPair]

/-- Exact first induced layer: the two parabolic cusps together carry mass
`1/2`. -/
theorem oneRunMass_eq_half : oneRunMass = 1 / 2 := by
  have hnorm : ‖(1 : ℝ) / 2‖ < 1 := by norm_num
  calc
    oneRunMass
        = ∑' n : ℕ, (2 * ((1 : ℝ) / 2) ^ 3) * ((1 : ℝ) / 2) ^ n := by
            unfold oneRunMass
            refine tsum_congr fun n => ?_
            rw [runHeight_single, show n + 1 + 2 = 3 + n by omega, pow_add]
            ring
    _ = (2 * ((1 : ℝ) / 2) ^ 3) * ∑' n : ℕ, ((1 : ℝ) / 2) ^ n := tsum_mul_left
    _ = 1 / 2 := by
          rw [tsum_geometric_of_norm_lt_one hnorm]
          norm_num

/-! ## The natural denominator exponent is at the Fibonacci knife-edge -/

/-- Sum of the invariant-coordinate exponents encountered on the unit-run
spine.  Clearing the corresponding Mersenne resolvents introduces factors on
this exponent scale. -/
def naturalRunDenominatorExponent (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, Nat.fib (j + 2)

/-- The natural exponent is exactly two below the minimum run height scale:
`F₂ + ... + F_{r+1} + 2 = F_{r+3}`. -/
theorem naturalRunDenominatorExponent_add_two (r : ℕ) :
    naturalRunDenominatorExponent r + 2 = Nat.fib (r + 3) := by
  induction r with
  | zero => norm_num [naturalRunDenominatorExponent, Nat.fib]
  | succ r ih =>
      change (∑ j ∈ Finset.range (r + 1), Nat.fib (j + 2)) + 2 = Nat.fib (r + 4)
      rw [Finset.sum_range_succ]
      change naturalRunDenominatorExponent r + Nat.fib (r + 2) + 2 = Nat.fib (r + 4)
      rw [@Nat.fib_add_two (r + 2)]
      change naturalRunDenominatorExponent r + Nat.fib (r + 2) + 2 =
        Nat.fib (r + 2) + Nat.fib (r + 3)
      omega

-- Axiom audit: the induced-run geometry is foundational only.
#print axioms sbPair_runWord
#print axioms runBoundaryPair_coprime
#print axioms runHeight_fib_lower
#print axioms runHeight_replicate_one
#print axioms runBoundaryPair_defectRunLengths
#print axioms runHeight_defectRunLengths
#print axioms runHeight_defect_linear_lower
#print axioms runHeight_defect_fib_sum_lower
#print axioms oneSiteWeight_eq_base_add
#print axioms runHeight_oneSiteDefect
#print axioms oneRunMass_eq_half
#print axioms naturalRunDenominatorExponent_add_two

end SternBrocotRunGeometry
