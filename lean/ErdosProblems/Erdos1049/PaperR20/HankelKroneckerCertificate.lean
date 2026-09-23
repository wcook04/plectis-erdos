import ErdosProblems.Erdos1049.PaperR20.CoefficientPencil
import ErdosProblems.Erdos1049.PaperR20.KroneckerCoefficientBound
import ErdosProblems.Erdos1049.PaperR20.TriangularPrefix

/-!
# Positive coefficients of the eight leading moment Hankel determinants

For `0 ≤ n ≤ 8` let `Q_n(t) = D_{n,0}(1 + t)`, where `D_{n,0}` is the determinant
of the `n × n` Hankel matrix of the coefficient moments `s_m`. This file proves
that every coefficient of `Q_n` is nonnegative and that its constant coefficient
is positive. Consequently `D_{n,0}(p) > 0` for every real `p ≥ 1`.

The proof evaluates at the single integer `T = 2 ^ 2929`.

* Every coefficient of `Q_n` has absolute value at most `n!` times a product of
  column bounds. The bounds come from coefficientwise majorants of the moments
  `s_m(1 + t)` and satisfy `2 · bound < T`.
* The integer `Q_n(T)` is the determinant of the integer Hankel matrix
  `(s_{i+j}(1 + T))`. The kernel computes that matrix from the Pascal
  recurrence for Gaussian binomials, and checks a triangular factorisation
  `M U = L` whose witness `U` is produced by fraction-free elimination. The
  witness is untrusted; only the checked identities enter the proof.
* The base-`T` digits of each `Q_n(T)` are all below `T / 2`, and the lowest is
  nonzero. By the bound above, these digits are exactly the coefficients of
  `Q_n`.

No coefficient list is stored: the kernel recovers the coefficients from the
digits of the single evaluation.
-/

namespace ErdosProblems.Erdos1049.PaperR20.HankelKronecker

open Polynomial Finset
open scoped BigOperators

/-! ## Finite sums, products and maxima used by the kernel computation -/

/-- `∑ i < n, f i`, by recursion on `n`. -/
def natSumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => natSumTo f n + f n

/-- `∏ i < n, f i`, by recursion on `n`. -/
def natProdTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => natProdTo f n * f n

/-- `∑ i < n, f i` for integer terms, by recursion on `n`. -/
def intSumTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => intSumTo f n + f n

/-- `max_{i < n} f i` (zero when `n = 0`), by recursion on `n`. -/
def natMaxTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (natMaxTo f n) (f n)

theorem natSumTo_eq (f : ℕ → ℕ) (n : ℕ) : natSumTo f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natSumTo, ih, sum_range_succ]

theorem natProdTo_eq (f : ℕ → ℕ) (n : ℕ) : natProdTo f n = ∏ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [natProdTo, ih, prod_range_succ]

theorem intSumTo_eq (f : ℕ → ℤ) (n : ℕ) : intSumTo f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [intSumTo, ih, sum_range_succ]

theorem le_natMaxTo (f : ℕ → ℕ) {n i : ℕ} (hi : i < n) : f i ≤ natMaxTo f n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [natMaxTo]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact (ih h).trans (le_max_left _ _)
      · subst h
        exact le_max_right _ _

theorem getD_map_range {α : Type*} (f : ℕ → α) (n k : ℕ) (d : α) :
    ((List.range n).map f).getD k d = if k < n then f k else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega)]

/-! ## Gaussian binomials by Pascal rows -/

/-- Gaussian binomials commute with ring homomorphisms. -/
theorem map_gaussBinom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : R) :
    ∀ n k, f (gaussBinom q n k) = gaussBinom (f q) n k
  | 0, 0 => by simp [gaussBinom]
  | 0, k + 1 => by simp [gaussBinom]
  | n + 1, 0 => by simp [gaussBinom]
  | n + 1, k + 1 => by
      rw [gaussBinom_succ, gaussBinom_succ, map_add, map_gaussBinom f q n (k + 1)]
      split_ifs
      · rw [map_mul, map_pow, map_gaussBinom f q n k]
      · rw [map_zero]

/-- Row `n + 1` of the Pascal table from row `n`, entries `k = 0, …, n + 1`. -/
def pascalNext (q n : ℕ) (row : List ℕ) : List ℕ :=
  1 :: (List.range (n + 1)).map (fun k => row.getD (k + 1) 0 + q ^ (n - k) * row.getD k 0)

/-- Row `n` of the Gaussian-binomial Pascal table at the natural number `q`. -/
def pascalRow (q : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => pascalNext q n (pascalRow q n)

/-- The Gaussian binomial at `q`, read from the Pascal row. -/
def gB (q n k : ℕ) : ℕ := (pascalRow q n).getD k 0

theorem gB_eq (q : ℕ) : ∀ n k, (gB q n k : ℤ) = gaussBinom (q : ℤ) n k := by
  intro n
  induction n with
  | zero =>
      intro k
      cases k with
      | zero => simp [gB, pascalRow]
      | succ k => simp [gB, pascalRow]
  | succ n ih =>
      intro k
      cases k with
      | zero => simp [gB, pascalRow, pascalNext]
      | succ k =>
          have hrow : gB q (n + 1) (k + 1) =
              if k < n + 1 then gB q n (k + 1) + q ^ (n - k) * gB q n k else 0 := by
            simp only [gB, pascalRow, pascalNext, List.getD_cons_succ, getD_map_range]
          rw [hrow, gaussBinom_succ]
          by_cases hk : k < n + 1
          · rw [if_pos hk, if_pos (by omega : k ≤ n)]
            push_cast
            rw [ih (k + 1), ih k]
          · rw [if_neg hk, if_neg (by omega : ¬ k ≤ n),
              gaussBinom_eq_zero_of_lt (q : ℤ) (by omega : n < k + 1)]
            simp

/-! ## The coefficient moments at a natural number -/

/-- `[m]_q! = ∏_{j < m} ∑_{i ≤ j} q^i`. -/
def qFactVal (q m : ℕ) : ℕ := natProdTo (fun j => natSumTo (fun i => q ^ i) (j + 1)) m

/-- The signed Gaussian-binomial sum `R_m(q)`. -/
def rVal (q m : ℕ) : ℤ :=
  intSumTo (fun k => (-1 : ℤ) ^ (m + k) *
    ((q ^ (k * (k + 1) / 2) * gB q m k * gB q (m + k) k : ℕ) : ℤ)) (m + 1)

/-- The coefficient moment `s_m(q) = ([m]_q!)^3 R_m(q)`. -/
def momentVal (q m : ℕ) : ℤ := (qFactVal q m : ℤ) ^ 3 * rVal q m

theorem eval_gaussBinom_X (x : ℤ) (n k : ℕ) :
    (gaussBinom (X : ℤ[X]) n k).eval x = gaussBinom x n k := by
  simpa using map_gaussBinom (Polynomial.evalRingHom x) (X : ℤ[X]) n k

theorem qFactVal_eq (q m : ℕ) :
    (qFactVal q m : ℤ) = (coefficientQFactorialPoly m).eval (q : ℤ) := by
  simp [qFactVal, natProdTo_eq, natSumTo_eq, coefficientQFactorialPoly, eval_prod,
    eval_finset_sum]

theorem rVal_eq (q m : ℕ) : rVal q m = (coefficientRPoly m).eval (q : ℤ) := by
  simp only [rVal, intSumTo_eq, coefficientRPoly, eval_finset_sum, eval_mul, eval_C,
    eval_pow, eval_X, eval_gaussBinom_X]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [gB_eq, gB_eq]
  ring

theorem momentVal_eq (q m : ℕ) : momentVal q m = (coefficientMomentPoly m).eval (q : ℤ) := by
  rw [momentVal, coefficientMomentPoly, eval_mul, eval_pow, qFactVal_eq, rVal_eq]

/-! ## Coefficient majorants of the translated moments -/

/-- A nonnegative-coefficient majorant of `s_m(1 + t)`. -/
noncomputable def momentMajPoly (m : ℕ) : ℤ[X] :=
  (∏ j ∈ range m, ∑ i ∈ range (j + 1), (X + 1 : ℤ[X]) ^ i) ^ 3 *
    ∑ k ∈ range (m + 1), (X + 1 : ℤ[X]) ^ (k * (k + 1) / 2) *
      gaussBinom (X + 1 : ℤ[X]) m k * gaussBinom (X + 1 : ℤ[X]) (m + k) k

theorem coeffNonneg_X_add_one : CoeffNonneg (X + 1 : ℤ[X]) :=
  CoeffNonneg.X.add CoeffNonneg.one

theorem coeffNonneg_gaussBinom_X_add_one :
    ∀ n k, CoeffNonneg (gaussBinom (X + 1 : ℤ[X]) n k)
  | 0, 0 => by simpa [gaussBinom] using CoeffNonneg.one
  | 0, k + 1 => by simpa [gaussBinom] using CoeffNonneg.zero
  | n + 1, 0 => by simpa [gaussBinom] using CoeffNonneg.one
  | n + 1, k + 1 => by
      rw [gaussBinom_succ]
      apply CoeffNonneg.add (coeffNonneg_gaussBinom_X_add_one n (k + 1))
      split_ifs
      · exact (coeffNonneg_X_add_one.pow _).mul (coeffNonneg_gaussBinom_X_add_one n k)
      · exact CoeffNonneg.zero

theorem coeffNonneg_qFactor (m : ℕ) :
    CoeffNonneg (∏ j ∈ range m, ∑ i ∈ range (j + 1), (X + 1 : ℤ[X]) ^ i) :=
  CoeffNonneg.prod _ fun _ _ => CoeffNonneg.sum _ fun i _ => coeffNonneg_X_add_one.pow i

theorem coeffNonneg_momentSummand (m k : ℕ) :
    CoeffNonneg ((X + 1 : ℤ[X]) ^ (k * (k + 1) / 2) *
      gaussBinom (X + 1 : ℤ[X]) m k * gaussBinom (X + 1 : ℤ[X]) (m + k) k) :=
  ((coeffNonneg_X_add_one.pow _).mul (coeffNonneg_gaussBinom_X_add_one m k)).mul
    (coeffNonneg_gaussBinom_X_add_one (m + k) k)

theorem coefficientMomentPoly_comp (m : ℕ) :
    (coefficientMomentPoly m).comp (X + 1) =
      (∏ j ∈ range m, ∑ i ∈ range (j + 1), (X + 1 : ℤ[X]) ^ i) ^ 3 *
        ∑ k ∈ range (m + 1), C ((-1 : ℤ) ^ (m + k)) *
          ((X + 1 : ℤ[X]) ^ (k * (k + 1) / 2) *
            gaussBinom (X + 1 : ℤ[X]) m k * gaussBinom (X + 1 : ℤ[X]) (m + k) k) := by
  have hg : ∀ n k, (gaussBinom (X : ℤ[X]) n k).comp (X + 1) = gaussBinom (X + 1 : ℤ[X]) n k := by
    intro n k
    simpa using map_gaussBinom (Polynomial.compRingHom (X + 1 : ℤ[X])) (X : ℤ[X]) n k
  rw [← coe_compRingHom_apply]
  simp only [coefficientMomentPoly, coefficientQFactorialPoly, coefficientRPoly, map_mul,
    map_pow, map_prod, map_sum]
  simp only [coe_compRingHom_apply, X_comp, C_comp, hg]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem momentMajPoly_majorant (m : ℕ) :
    CoeffMajorant ((coefficientMomentPoly m).comp (X + 1)) (momentMajPoly m) := by
  rw [coefficientMomentPoly_comp, momentMajPoly]
  apply CoeffMajorant.mul ((coeffNonneg_qFactor m).pow 3).majorant_self
  apply CoeffMajorant.sum
  intro k _
  apply CoeffMajorant.C_mul_of_abs_le_one (by simp)
  exact (coeffNonneg_momentSummand m k).majorant_self

/-- The value at `t = 1` (that is, `p = 2`) of the moment majorant. -/
def momentMajVal (m : ℕ) : ℕ :=
  qFactVal 2 m ^ 3 *
    natSumTo (fun k => 2 ^ (k * (k + 1) / 2) * gB 2 m k * gB 2 (m + k) k) (m + 1)

theorem momentMajPoly_eval_one (m : ℕ) : (momentMajPoly m).eval 1 = momentMajVal m := by
  have hg : ∀ n k, (gaussBinom (X + 1 : ℤ[X]) n k).eval 1 = gaussBinom (2 : ℤ) n k := by
    intro n k
    have h := map_gaussBinom (Polynomial.evalRingHom (1 : ℤ)) (X + 1 : ℤ[X]) n k
    simp only [coe_evalRingHom, eval_add, eval_X, eval_one] at h
    rw [h]
    norm_num
  simp only [momentMajPoly, momentMajVal, qFactVal, natProdTo_eq, natSumTo_eq, eval_mul,
    eval_pow, eval_prod, eval_finset_sum, eval_add, eval_X, eval_one, hg]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [gB_eq, gB_eq]
  norm_num

/-- `n!` times the product over columns of the largest majorant value in that column. -/
def detBound (n : ℕ) : ℕ :=
  n.factorial * natProdTo (fun j => natMaxTo (fun i => momentMajVal (i + j)) n) n

theorem translatedHankel_eq_det (n : ℕ) :
    (coefficientHankelDetPoly n 0).comp (X + 1) =
      Matrix.det (Matrix.of fun i j : Fin n => (coefficientMomentPoly (i.val + j.val)).comp (X + 1)) := by
  rw [coefficientHankelDetPoly, ← coe_compRingHom_apply, RingHom.map_det]
  refine congrArg Matrix.det ?_
  ext i j
  simp

theorem translatedHankel_coeff_abs_le (n k : ℕ) :
    |((coefficientHankelDetPoly n 0).comp (X + 1)).coeff k| ≤ detBound n := by
  rw [translatedHankel_eq_det]
  have h := det_coeff_abs_le_of_majorant
    (Matrix.of fun i j : Fin n => (coefficientMomentPoly (i.val + j.val)).comp (X + 1))
    (Matrix.of fun i j : Fin n => momentMajPoly (i.val + j.val))
    (fun i j => momentMajPoly_majorant (i.val + j.val))
    (fun j => (natMaxTo (fun i => momentMajVal (i + j.val)) n : ℤ))
    (fun i j => by
      simp only [Matrix.of_apply, momentMajPoly_eval_one]
      exact_mod_cast le_natMaxTo (fun i => momentMajVal (i + j.val)) i.isLt) k
  refine h.trans (le_of_eq ?_)
  rw [detBound, natProdTo_eq]
  push_cast
  rw [Fin.prod_univ_eq_prod_range (fun j => (natMaxTo (fun i => momentMajVal (i + j)) n : ℤ)) n]

/-! ## Evaluation at a natural number -/

theorem translatedHankel_eval (n T : ℕ) :
    ((coefficientHankelDetPoly n 0).comp (X + 1)).eval (T : ℤ) =
      Matrix.det (Matrix.of fun i j : Fin n => momentVal (1 + T) (i.val + j.val)) := by
  rw [eval_comp, eval_add, eval_X, eval_one, coefficientHankelDetPoly, ← coe_evalRingHom,
    RingHom.map_det]
  refine congrArg Matrix.det ?_
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, coe_evalRingHom,
    add_zero, momentVal_eq]
  congr 1
  push_cast
  ring

/-! ## The integer triangular certificate -/

/-- Moment values `s_0(q), …, s_M(q)`. -/
def momentVec (q M : ℕ) : List ℤ := (List.range (M + 1)).map (momentVal q)

/-- Rows of `[M | I]` for the Hankel matrix `M = (mv_{i+j})`. -/
def augmentRows (N : ℕ) (mv : List ℤ) : List (List ℤ) :=
  (List.range N).map (fun i =>
    (List.range N).map (fun j => mv.getD (i + j) 0) ++
      (List.range N).map (fun j => if i = j then (1 : ℤ) else 0))

/-- One step of fraction-free elimination with pivot row `k`. This producer is
untrusted: its output enters the proof only through the checked identities. -/
def bareissStep (k : ℕ) (prev : ℤ) (rows : List (List ℤ)) : List (List ℤ) :=
  let pr := rows.getD k []
  let p := pr.getD k 0
  rows.mapIdx (fun i row => if i ≤ k then row else
    let a := row.getD k 0
    List.zipWith (fun x y => (p * x - a * y) / prev) row pr)

def bareissLoop : ℕ → ℕ → ℤ → List (List ℤ) → List (List ℤ)
  | 0, _, _, rows => rows
  | fuel + 1, k, prev, rows =>
      bareissLoop fuel (k + 1) ((rows.getD k []).getD k 0) (bareissStep k prev rows)

/-- Hankel entry `(i, j)` read from the moment vector. -/
def Mv (mv : List ℤ) (i j : ℕ) : ℤ := mv.getD (i + j) 0

/-- Witness entry `U_{kj}`: row `j` of the elimination multiplier, column `k`. -/
def Uv (N : ℕ) (rows : List (List ℤ)) (k j : ℕ) : ℤ := (rows.getD j []).getD (N + k) 0

/-- Claimed leading determinants: `D 0 = 1` and `D (k+1)` the `k`-th pivot. -/
def Dv (rows : List (List ℤ)) (k : ℕ) : ℤ :=
  if k = 0 then 1 else (rows.getD (k - 1) []).getD (k - 1) 0

/-- Entry `(i, j)` of `M U`. -/
def dotMU (N : ℕ) (mv : List ℤ) (rows : List (List ℤ)) (i j : ℕ) : ℤ :=
  intSumTo (fun k => Mv mv i k * Uv N rows k j) N

/-- The triangular identities checked by the kernel. -/
abbrev TriFacts (N : ℕ) (mv : List ℤ) (rows : List (List ℤ)) : Prop :=
  ∀ i < N, ∀ j < N, (j < i → Uv N rows i j = 0) ∧ (i < j → dotMU N mv rows i j = 0) ∧
    (i = j → Uv N rows i i = Dv rows i ∧ dotMU N mv rows i i = Dv rows (i + 1) ∧
      Dv rows i ≠ 0)

theorem det_leading_eq_Dv {N : ℕ} {mv : List ℤ} {rows : List (List ℤ)}
    (h : TriFacts N mv rows) (n : ℕ) (hn : n ≤ N) :
    Matrix.det (Matrix.of fun i j : Fin n => Mv mv i.val j.val) = Dv rows n := by
  have hmul : ∀ i j : Fin N,
      ((Matrix.of fun a b : Fin N => Mv mv a.val b.val) *
        (Matrix.of fun a b : Fin N => Uv N rows a.val b.val)) i j = dotMU N mv rows i.val j.val := by
    intro i j
    rw [Matrix.mul_apply, dotMU, intSumTo_eq]
    exact Fin.sum_univ_eq_sum_range (fun k => Mv mv i.val k * Uv N rows k j.val) N
  have key := leading_determinant_of_triangular_certificate
    (Matrix.of fun a b : Fin N => Mv mv a.val b.val)
    (Matrix.of fun a b : Fin N => Uv N rows a.val b.val) (Dv rows) (by simp [Dv])
    (fun i j hij => (h i.val i.isLt j.val j.isLt).1 hij)
    (fun i j hij => by rw [hmul]; exact (h i.val i.isLt j.val j.isLt).2.1 hij)
    (fun i => ((h i.val i.isLt i.val i.isLt).2.2 rfl).1)
    (fun i => by rw [hmul]; exact ((h i.val i.isLt i.val i.isLt).2.2 rfl).2.1)
    (fun i => ((h i.val i.isLt i.val i.isLt).2.2 rfl).2.2) n hn
  rw [← key]
  rfl

/-! ## Digit checks -/

/-- `V ≥ 0`, `V < 2^(K L)`, the lowest base-`2^K` digit of `V` is nonzero, and every
base-`2^K` digit below position `L` is below `2^(K-1)`. -/
def digitOk (K L : ℕ) (V : ℤ) : Bool :=
  decide (0 ≤ V) && ((V.toNat >>> (K * L)) == 0) && (V.toNat % 2 ^ K != 0) &&
    (List.range L).all (fun i => decide (2 * ((V.toNat >>> (K * i)) % 2 ^ K) < 2 ^ K))

theorem digitOk_sound {K L : ℕ} {V : ℤ} (h : digitOk K L V = true) :
    0 ≤ V ∧ V.toNat < (2 ^ K) ^ L ∧ V.toNat % 2 ^ K ≠ 0 ∧
      ∀ i < L, 2 * (V.toNat / (2 ^ K) ^ i % 2 ^ K) < 2 ^ K := by
  simp only [digitOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  refine ⟨h0, ?_, h2, fun i hi => ?_⟩
  · rw [Nat.shiftRight_eq_div_pow] at h1
    rw [← pow_mul]
    by_contra hge
    have hpos : 0 < 2 ^ (K * L) := by positivity
    have := Nat.div_pos (not_lt.mp hge) hpos
    omega
  · have hi' := h3 i hi
    rwa [Nat.shiftRight_eq_div_pow, pow_mul] at hi'

/-! ## The certified evaluation -/

/-- `T = 2 ^ certK` exceeds twice every coefficient bound at ranks `n ≤ 8`. -/
def certK : ℕ := 2929

/-- Number of base-`T` digits checked; `D_{8,0}` has degree `1624`. -/
def certL : ℕ := 1630

/-- `s_0(1 + T), …, s_14(1 + T)`. -/
def certMv : List ℤ := momentVec (1 + 2 ^ certK) 14

/-- Output of the untrusted elimination on `[M | I]`, `M = (s_{i+j}(1 + T))_{i,j<8}`. -/
def certRows : List (List ℤ) := bareissLoop 8 0 1 (augmentRows 8 certMv)

/-- The coefficient bounds are below `T / 2` at every rank `n ≤ 8`. -/
theorem cert_bound : ∀ n < 9, 2 * detBound n < 2 ^ certK := by decide +kernel

/-- The single kernel computation: the triangular identities for the integer
Hankel matrix at `1 + T`, and the digit conditions for every pivot. -/
theorem cert_facts :
    TriFacts 8 certMv certRows ∧ ∀ n < 9, digitOk certK certL (Dv certRows n) = true := by
  decide +kernel

theorem certMv_entry {i j : ℕ} (hi : i < 8) (hj : j < 8) :
    Mv certMv i j = momentVal (1 + 2 ^ certK) (i + j) := by
  rw [Mv, certMv, momentVec, getD_map_range, if_pos (by omega)]

/-- Every coefficient of `D_{n,0}(1 + t)` is a base-`T` digit of the certified value. -/
theorem translatedHankel_coeff_eq_digit (n : ℕ) (hn : n ≤ 8) (k : ℕ) :
    ((coefficientHankelDetPoly n 0).comp (X + 1)).coeff k =
      (((Dv certRows n).toNat / (2 ^ certK) ^ k % 2 ^ certK : ℕ) : ℤ) := by
  obtain ⟨htri, hdig⟩ := cert_facts
  obtain ⟨hV0, hVlt, _, hdigits⟩ := digitOk_sound (hdig n (by omega))
  apply coeff_eq_digit_of_eval _ (2 ^ certK) ((Dv certRows n).toNat) certL
    (by positivity)
  · intro k
    have hb := translatedHankel_coeff_abs_le n k
    have hc := cert_bound n (by omega)
    have hc' : (2 : ℤ) * (detBound n : ℤ) < ((2 ^ certK : ℕ) : ℤ) := by exact_mod_cast hc
    linarith
  · rw [translatedHankel_eval, Int.toNat_of_nonneg hV0, ← det_leading_eq_Dv htri n hn]
    congr 1
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply,
      certMv_entry (lt_of_lt_of_le i.isLt hn) (lt_of_lt_of_le j.isLt hn)]
  · exact hVlt
  · exact hdigits

/-- Coefficient positivity: `D_{n,0}(1 + t)` has nonnegative coefficients and a
positive constant coefficient, for `0 ≤ n ≤ 8`. -/
theorem translatedHankel_coeff_nonneg (n : ℕ) (hn : n ≤ 8) :
    (∀ k, 0 ≤ ((coefficientHankelDetPoly n 0).comp (X + 1)).coeff k) ∧
      0 < ((coefficientHankelDetPoly n 0).comp (X + 1)).coeff 0 := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [translatedHankel_coeff_eq_digit n hn k]
    exact Nat.cast_nonneg _
  · rw [translatedHankel_coeff_eq_digit n hn 0]
    obtain ⟨_, hdig⟩ := cert_facts
    obtain ⟨_, _, hlow, _⟩ := digitOk_sound (hdig n (by omega))
    simp only [pow_zero, Nat.div_one]
    exact_mod_cast Nat.pos_of_ne_zero hlow

end ErdosProblems.Erdos1049.PaperR20.HankelKronecker

namespace ErdosProblems.Erdos1049.PaperR20

open Polynomial

/-- The leading Hankel determinants `D_{n,0}` of the coefficient moments are
positive at every real `p ≥ 1`, for `0 ≤ n ≤ 8`. -/
theorem coefficientHankelDetPoly_shift0_pos {p : ℝ} (hp : 1 ≤ p) (n : ℕ) (hn : n ≤ 8) :
    0 < (coefficientHankelDetPoly n 0).eval₂ (Int.castRingHom ℝ) p := by
  obtain ⟨hcoeff, hconst⟩ := HankelKronecker.translatedHankel_coeff_nonneg n hn
  rw [coefficientHankelDetPoly_eval]
  exact coefficientHankelDet_pos_of_certificate hp n 0 hcoeff hconst

end ErdosProblems.Erdos1049.PaperR20
