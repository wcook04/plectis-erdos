import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import ErdosProblems.Erdos1049.GaussianCoefficientsR11
import ErdosProblems.Erdos1049.GaussianDegreeR12
import ErdosProblems.Erdos1049.PaperR20.CoefficientPencil
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Tactic

/-!
# Erdős #1049: the moment weights as a product of two finite sums

Paper restatement of `long1049:prop:rogers-factorisation` (core.tex, subsection "The size of
`V_N^*` at a fixed base"), in the form the paper states it: polynomial identities in the
indeterminate `q`.

## The objects

* `ℚ⟦q⟧` is `PowerSeries ℚ` with indeterminate `qq`; `(q;q)_n` is the tree's finite
  `q`-Pochhammer `qPochhammer q q n` (`qfac`).
* `ℚ⟦q⟧⟦w⟧` is `PowerSeries (PowerSeries ℚ)` with indeterminate `ww`, carrying the product
  (coefficientwise) topology; `(x;q)_∞ = ∏'_{i ≥ 0} (1 - x q^i)` is a genuine infinite
  product there (`qPochInf`, multipliable for every `x`).
* `G_q(w) = (w;q)_∞^{-3} ∑'_{t ≥ 0} w^t/(q;q)_t · (q^t w^2;q)_∞/(q^t w;q)_∞^2`
  (`momentGenFun`), and `γ_k(q) = [w^k] G_q(w) ∈ ℚ⟦q⟧` (`momentWeight`).
* `R_k^{(r)}(q) = ∑_{n_1+⋯+n_r=k} (q;q)_k / ∏_{j ≤ r} (q;q)_{n_j}` (`rogersR`), the sum
  over `Finset.Nat.antidiagonalTuple r k`.

## The proof

Euler's product formula is proved for `(a w^j; q)_∞` by the functional equation and a
`q`-adic uniqueness argument (`qPochInf_C_mul_pow`).  The `w^2`-product is removed by a finite
`q`-binomial identity (`qbinomial_w`), which gives
`G_q = E(w)^2 ∑_{t,d} w^{t+d}/((q;q)_t (q;q)_d) E(q^{t+d} w) E(q^t w)` with `E = 1/(w;q)_∞`.
On the other side, `∑_k R_k^{(2)} R_k^{(3)}/(q;q)_k w^k = ∑_r w^r/(q;q)_r ∂_q^r E(w)^3`, and
two applications of the `q`-Leibniz rule for the `q`-derivative `∂_q` (`qD_iter_eE_mul`) give
the same double sum.  The polynomial statements reuse the tree's Gaussian-binomial lemmas
(nonnegative coefficients, monic of degree `k(n-k)`, value `binom n k` at `q = 1`).

The tree's `coefficientQFactorialPoly m` is the `q`-factorial `[m]_q!`, which differs from
`(q;q)_m` by the factor `(1-q)^m` (`qfac_eq_coefficientQFactorialPoly`); it is therefore not
the `(q;q)_k` of the proposition.  The tree's coefficient moments `s_m` are a different
sequence from the positive-measure weights `γ_k`.

The analytic consequences stated after "Consequently" (the bounds `P^5 c_k ≤ a_k ≤ P^{-1} c_k`
and `a_{k+h}/a_k ≤ P^{-6}(1+h)^3` for real `0 < q < 1`) are not formalised here; the
integrality consequence `(q;q)_k γ_k ∈ ℤ[q]` is.
-/

noncomputable section

namespace ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation

open PowerSeries Finset
open ErdosProblems.Erdos1049 (qPochhammer gaussBinom)

/-! ### `q`-factorials in `ℚ⟦q⟧` -/

/-- The indeterminate `q` of `ℚ⟦q⟧`. -/
abbrev qq : PowerSeries ℚ := PowerSeries.X

/-- `(q;q)_n = ∏_{i < n} (1 - q^{i+1})`, the tree's finite `q`-Pochhammer `qPochhammer q q n`. -/
def qfac (n : ℕ) : PowerSeries ℚ := qPochhammer qq qq n

/-- `1 / (q;q)_n` in `ℚ⟦q⟧`. -/
def ifac (n : ℕ) : PowerSeries ℚ := (qfac n)⁻¹

lemma qfac_zero : qfac 0 = 1 := rfl

lemma qfac_succ (n : ℕ) : qfac (n + 1) = qfac n * (1 - qq ^ (n + 1)) := by
  rw [qfac, qfac, ErdosProblems.Erdos1049.qPochhammer_succ, ← pow_succ']

lemma constantCoeff_qfac (n : ℕ) : constantCoeff (qfac n) = 1 := by
  induction n with
  | zero => simp [qfac_zero]
  | succ n ih =>
      rw [qfac_succ, map_mul, ih, map_sub, map_one, map_pow, constantCoeff_X]
      simp

lemma qfac_mul_ifac (n : ℕ) : qfac n * ifac n = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_qfac]; exact one_ne_zero)

lemma ifac_mul_qfac (n : ℕ) : ifac n * qfac n = 1 := by
  rw [mul_comm]; exact qfac_mul_ifac n

lemma ifac_zero : ifac 0 = 1 := by
  have h := qfac_mul_ifac 0
  rwa [qfac_zero, one_mul] at h

lemma ifac_succ (n : ℕ) : ifac n = ifac (n + 1) * (1 - qq ^ (n + 1)) := by
  have h1 := qfac_mul_ifac n
  have h2 := qfac_mul_ifac (n + 1)
  rw [qfac_succ] at h2
  linear_combination (-ifac n) * h2 + ((1 - qq ^ (n + 1)) * ifac (n + 1)) * h1

lemma gaussBinom_eq {n k : ℕ} (hk : k ≤ n) :
    gaussBinom qq n k = qfac n * ifac k * ifac (n - k) := by
  have h := ErdosProblems.Erdos1049.gaussBinom_mul_qPochhammer_qPochhammer qq n k hk
  have h1 := qfac_mul_ifac k
  have h2 := qfac_mul_ifac (n - k)
  change gaussBinom qq n k * qfac k * qfac (n - k) = qfac n at h
  linear_combination (ifac k * ifac (n - k)) * h - gaussBinom qq n k * h1 -
    (gaussBinom qq n k * qfac k * ifac k) * h2

lemma ifac_mul_gaussBinom {n k : ℕ} (hk : k ≤ n) :
    ifac n * gaussBinom qq n k = ifac k * ifac (n - k) := by
  rw [gaussBinom_eq hk]
  linear_combination (ifac k * ifac (n - k)) * ifac_mul_qfac n

/-! ### The ring `ℚ⟦q⟧⟦w⟧` and the Euler series -/

/-- Formal power series in `w` over `ℚ⟦q⟧`. -/
abbrev BW := PowerSeries (PowerSeries ℚ)

/-- The indeterminate `w`. -/
abbrev ww : BW := PowerSeries.X

/-- `∑_n w^n / (q;q)_n`. -/
def eE : BW := mk fun n => ifac n

/-- `∑_n (-1)^n q^{n(n-1)/2} w^n / (q;q)_n`. -/
def eP : BW := mk fun n => (-1) ^ n * qq ^ (n.choose 2) * ifac n

/-- `(w;q)_j = ∏_{i < j} (1 - w q^i)`, the tree's finite `q`-Pochhammer in `ℚ⟦q⟧⟦w⟧`. -/
def wPoch (j : ℕ) : BW := qPochhammer (C qq) ww j

lemma coeff_eE (n : ℕ) : coeff n eE = ifac n := coeff_mk _ _

lemma coeff_eP (n : ℕ) : coeff n eP = (-1) ^ n * qq ^ (n.choose 2) * ifac n := coeff_mk _ _

lemma eP_mul_eE : eP * eE = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_mul, coeff_one]
  simp only [coeff_eE, coeff_eP]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ k ∈ range n.succ,
      (-1 : PowerSeries ℚ) ^ (k, n - k).1 * qq ^ ((k, n - k).1.choose 2) * ifac (k, n - k).1 *
        ifac (k, n - k).2 =
      ifac n * ErdosProblems.Erdos1049.qBinomialTerm qq (1 : PowerSeries ℚ) n k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    simp only [ErdosProblems.Erdos1049.qBinomialTerm, one_pow, mul_one]
    rw [← mul_assoc, ← mul_assoc, ifac_mul_gaussBinom hkn]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    ← ErdosProblems.Erdos1049.qPochhammer_eq_sum]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ErdosProblems.Erdos1049.qPochhammer, ifac_zero]
  · rw [ErdosProblems.Erdos1049.qPochhammer_one qq hn, mul_zero, if_neg hn.ne']

lemma eE_mul_eP : eE * eP = 1 := by rw [mul_comm]; exact eP_mul_eE

lemma rescale_q_eE : rescale qq eE = (1 - ww) * eE := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_rescale, coeff_eE, sub_mul, one_mul, map_sub, coeff_eE]
  cases n with
  | zero => simp
  | succ n =>
      rw [coeff_succ_X_mul, coeff_eE, ifac_succ n]
      ring

lemma rescale_rescale_eE (a b : PowerSeries ℚ) :
    rescale b (rescale a eE) = rescale (a * b) eE := rescale_rescale _ _ _

/-- `E(w) (w;q)_j = E(q^j w)`. -/
lemma eE_mul_wPoch (j : ℕ) : eE * wPoch j = rescale (qq ^ j) eE := by
  induction j with
  | zero => simp [wPoch, ErdosProblems.Erdos1049.qPochhammer]
  | succ j ih =>
      rw [wPoch, ErdosProblems.Erdos1049.qPochhammer_succ, ← wPoch, ← mul_assoc, ih]
      have h1 : rescale (qq ^ (j + 1)) eE = rescale (qq ^ j) (rescale qq eE) := by
        rw [rescale_rescale, ← pow_succ']
      rw [h1, rescale_q_eE, map_mul, map_sub, map_one, rescale_X, map_pow]
      ring

/-- Gaussian binomials commute with ring homomorphisms. -/
lemma map_gaussBinom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : R) :
    ∀ n k, f (gaussBinom q n k) = gaussBinom (f q) n k
  | 0, 0 => by simp [gaussBinom]
  | 0, k + 1 => by simp [gaussBinom]
  | n + 1, 0 => by simp [gaussBinom]
  | n + 1, k + 1 => by
      rw [ErdosProblems.Erdos1049.gaussBinom_succ, ErdosProblems.Erdos1049.gaussBinom_succ,
        map_add, map_gaussBinom f q n (k + 1)]
      split_ifs
      · rw [map_mul, map_pow, map_gaussBinom f q n k]
      · rw [map_zero]

lemma coeff_wPoch (j l : ℕ) :
    coeff l (wPoch j) = gaussBinom qq j l * (-1) ^ l * qq ^ (l.choose 2) := by
  rw [wPoch, ErdosProblems.Erdos1049.qPochhammer_eq_sum, map_sum]
  have hterm : ∀ k ∈ range (j + 1),
      coeff l (ErdosProblems.Erdos1049.qBinomialTerm (C qq) ww j k) =
        if l = k then gaussBinom qq j k * (-1) ^ k * qq ^ (k.choose 2) else 0 := by
    intro k _
    rw [ErdosProblems.Erdos1049.qBinomialTerm, ← map_gaussBinom (C : PowerSeries ℚ →+* BW),
      ← map_pow, show (-1 : BW) ^ k = C ((-1) ^ k) by simp, ← map_mul, ← map_mul,
      coeff_C_mul_X_pow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [ErdosProblems.Erdos1049.gaussBinom_eq_zero_of_lt qq (by
      simp only [mem_range, not_lt] at h; omega)]
    ring

/-! ### Sums `∑_i w^i F_i` -/

/-- `wsum F = ∑_i w^i F_i`, the sum converging `w`-adically. -/
def wsum (F : ℕ → BW) : BW := mk fun n => ∑ i ∈ range (n + 1), coeff (n - i) (F i)

lemma coeff_wsum (F : ℕ → BW) (n : ℕ) :
    coeff n (wsum F) = ∑ i ∈ range (n + 1), coeff (n - i) (F i) := coeff_mk _ _

open scoped PowerSeries.WithPiTopology

lemma hasSum_wsum (F : ℕ → BW) : HasSum (fun i => ww ^ i * F i) (wsum F) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro n
  have h : coeff n (wsum F) = ∑ i ∈ range (n + 1), coeff n (ww ^ i * F i) := by
    rw [coeff_wsum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [coeff_X_pow_mul', if_pos (Nat.lt_succ_iff.mp (mem_range.mp hi))]
  rw [h]
  apply hasSum_sum_of_ne_finset_zero
  intro i hi
  rw [coeff_X_pow_mul', if_neg]
  simp only [mem_range, not_lt] at hi
  omega

lemma mul_wsum (G : BW) (F : ℕ → BW) : G * wsum F = wsum (fun i => G * F i) := by
  apply HasSum.unique _ (hasSum_wsum (fun i => G * F i))
  convert (hasSum_wsum F).mul_left G using 1
  ext1 i
  ring

lemma wsum_mul (G : BW) (F : ℕ → BW) : wsum F * G = wsum (fun i => F i * G) := by
  rw [mul_comm, mul_wsum]
  simp_rw [mul_comm G]

lemma wsum_add (F G : ℕ → BW) : wsum (fun i => F i + G i) = wsum F + wsum G := by
  refine PowerSeries.ext fun n => ?_
  simp [coeff_wsum, Finset.sum_add_distrib]

lemma wsum_sum {ι : Type*} (s : Finset ι) (F : ι → ℕ → BW) :
    wsum (fun i => ∑ x ∈ s, F x i) = ∑ x ∈ s, wsum (F x) := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_wsum, map_sum]
  rw [Finset.sum_comm]

lemma wsum_C (c : ℕ → PowerSeries ℚ) : wsum (fun i => C (c i)) = mk c := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_wsum, coeff_mk, Finset.sum_eq_single n]
  · simp
  · intro i hi hin
    rw [coeff_C, if_neg]
    simp only [mem_range] at hi
    omega
  · intro h; simp at h

lemma wsum_C_mul (c : ℕ → PowerSeries ℚ) (H : BW) :
    wsum (fun i => C (c i) * H) = mk c * H := by
  rw [← wsum_C, wsum_mul]

lemma sum_triangle {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ → M) (n : ℕ) :
    ∑ m ∈ range (n + 1), ∑ i ∈ range (m + 1), g i m =
      ∑ i ∈ range (n + 1), ∑ j ∈ range (n - i + 1), g i (i + j) := by
  have h1 : ∑ m ∈ range (n + 1), ∑ i ∈ range (m + 1), g i m =
      ∑ m ∈ Ico 0 (n + 1), ∑ i ∈ Ico 0 (m + 1), g i m := by
    simp only [Finset.range_eq_Ico]
  have h2 : ∑ i ∈ range (n + 1), ∑ j ∈ range (n - i + 1), g i (i + j) =
      ∑ i ∈ Ico 0 (n + 1), ∑ j ∈ range (n + 1 - i), g i (i + j) := by
    rw [Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [mem_Ico] at hi
    rw [show n + 1 - i = n - i + 1 by omega]
  rw [h1, h2, ← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]

/-- `∑_n w^n ∑_{i+j=n} F_{i,j} = ∑_i w^i ∑_j w^j F_{i,j}`. -/
lemma wsum_antidiag (F : ℕ → ℕ → BW) :
    wsum (fun n => ∑ p ∈ antidiagonal n, F p.1 p.2) = wsum (fun i => wsum (fun j => F i j)) := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_wsum, map_sum]
  have hL : ∀ m ∈ range (n + 1),
      ∑ p ∈ antidiagonal m, coeff (n - m) (F p.1 p.2) =
        ∑ i ∈ range (m + 1), coeff (n - m) (F i (m - i)) := by
    intro m _
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff (n - m) (F i j)) m
  rw [Finset.sum_congr rfl hL,
    sum_triangle (fun i m => coeff (n - m) (F i (m - i))) n]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_sub_cancel_left, Nat.sub_sub]

lemma wsum_comm (F : ℕ → ℕ → BW) :
    wsum (fun i => wsum (fun j => F i j)) = wsum (fun j => wsum (fun i => F i j)) := by
  rw [← wsum_antidiag, ← wsum_antidiag]
  congr 1
  ext1 n
  rw [← Finset.Nat.sum_antidiagonal_swap]
  rfl

lemma wsum_congr {F G : ℕ → BW} (h : ∀ i, F i = G i) : wsum F = wsum G := by
  rw [funext h]

/-! ### The infinite products -/

/-- `(x;q)_∞ = ∏_{i ≥ 0} (1 - x q^i)` in `ℚ⟦q⟧⟦w⟧`, an infinite product in the product
(coefficientwise) topology. -/
def qPochInf (x : BW) : BW := ∏' i : ℕ, (1 - x * C (qq ^ i))

lemma C_pow_dvd_iff {a : ℕ} {f : BW} : C (qq ^ a) ∣ f ↔ ∀ k, qq ^ a ∣ coeff k f := by
  constructor
  · rintro ⟨g, rfl⟩ k
    rw [coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    refine ⟨mk fun k => Classical.choose (h k), ?_⟩
    refine PowerSeries.ext fun k => ?_
    rw [coeff_C_mul, coeff_mk]
    exact Classical.choose_spec (h k)

lemma coeff_coeff_eq_zero_of_dvd {a : ℕ} {f : BW} (h : C (qq ^ a) ∣ f) (k : ℕ) {m : ℕ}
    (hm : m < a) : coeff m (coeff k f) = 0 :=
  (PowerSeries.X_pow_dvd_iff.mp (C_pow_dvd_iff.mp h k)) m hm

lemma eq_zero_of_forall_dvd {f : BW} (h : ∀ a, C (qq ^ a) ∣ f) : f = 0 := by
  refine PowerSeries.ext fun k => PowerSeries.ext fun m => ?_
  rw [map_zero, map_zero]
  exact coeff_coeff_eq_zero_of_dvd (h (m + 1)) k (Nat.lt_succ_self m)

lemma multipliable_qPochInf (x : BW) : Multipliable (fun i : ℕ => 1 - x * C (qq ^ i)) := by
  have hsum : Summable (fun s : Finset ℕ => ∏ i ∈ s, -(x * C (qq ^ i))) := by
    rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
    intro k
    rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
    intro m
    apply summable_of_hasFiniteSupport
    refine Set.Finite.subset (Finset.finite_toSet (range (m + 1)).powerset) ?_
    intro s hs
    rw [Function.mem_support] at hs
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    intro i hi
    by_contra hmi
    apply hs
    have hdvd : C (qq ^ i) ∣ ∏ j ∈ s, -(x * C (qq ^ j)) :=
      Dvd.dvd.trans ⟨-x, by ring⟩ (Finset.dvd_prod_of_mem _ hi)
    exact coeff_coeff_eq_zero_of_dvd hdvd k (by simp only [mem_range] at hmi; omega)
  have h := multipliable_one_add_of_summable_prod hsum
  simpa [sub_eq_add_neg] using h

lemma hasProd_qPochInf (x : BW) : HasProd (fun i : ℕ => 1 - x * C (qq ^ i)) (qPochInf x) :=
  (multipliable_qPochInf x).hasProd

/-- `(x;q)_∞ = (1 - x) (qx;q)_∞`. -/
lemma qPochInf_eq (x : BW) : qPochInf x = (1 - x) * qPochInf (C qq * x) := by
  unfold qPochInf
  have hshift : (fun i : ℕ => 1 - x * C (qq ^ (i + 1))) =
      (fun i : ℕ => 1 - C qq * x * C (qq ^ i)) := by
    funext i
    rw [pow_succ', map_mul]
    ring
  rw [tprod_eq_zero_mul' (by rw [hshift]; exact multipliable_qPochInf (C qq * x)), hshift]
  simp

/-- Every factor of `(q^a y; q)_∞` is `1` modulo `q^a`, hence so is the product. -/
lemma dvd_qPochInf_sub_one (a : ℕ) (y : BW) : C (qq ^ a) ∣ qPochInf (C (qq ^ a) * y) - 1 := by
  set f : ℕ → BW := fun i => 1 - C (qq ^ a) * y * C (qq ^ i) with hf
  have hpart : ∀ N, C (qq ^ a) ∣ (∏ i ∈ range N, f i) - 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.prod_range_succ]
        have e : (∏ i ∈ range N, f i) * f N - 1 =
            ((∏ i ∈ range N, f i) - 1) * f N + (-(y * C (qq ^ N))) * C (qq ^ a) := by
          simp only [hf]; ring
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_left ih _) (dvd_mul_left _ _)
  rw [C_pow_dvd_iff]
  intro k
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  have htend := (hasProd_qPochInf (C (qq ^ a) * y)).tendsto_prod_nat
  have hcont : Continuous (fun g : BW => coeff m (coeff k g)) :=
    (PowerSeries.WithPiTopology.continuous_coeff ℚ m).comp
      (PowerSeries.WithPiTopology.continuous_coeff (PowerSeries ℚ) k)
  have h1 := (hcont.tendsto _).comp htend
  have hconst : ∀ N, coeff m (coeff k (∏ i ∈ range N, f i)) = coeff m (coeff k (1 : BW)) := by
    intro N
    have := coeff_coeff_eq_zero_of_dvd (hpart N) k hm
    rw [map_sub, map_sub] at this
    exact sub_eq_zero.mp this
  have h2 : Filter.Tendsto (fun N => coeff m (coeff k (∏ i ∈ range N, f i))) Filter.atTop
      (nhds (coeff m (coeff k (1 : BW)))) := by
    simp_rw [hconst]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique h1 h2
  rw [map_sub, map_sub]
  exact sub_eq_zero.mpr heq

/-! ### Euler's product formula -/

lemma eP_eq : eP = (1 - ww) * rescale qq eP := by
  refine PowerSeries.ext fun n => ?_
  rw [sub_mul, one_mul, map_sub, coeff_rescale]
  cases n with
  | zero => simp [coeff_eP]
  | succ n =>
      rw [coeff_succ_X_mul, coeff_rescale, coeff_eP, coeff_eP, ifac_succ n,
        ErdosProblems.Erdos1049.choose_two_succ]
      ring

/-- The explicit series of `(a w^j; q)_∞`. -/
def eulerP (a : PowerSeries ℚ) (j : ℕ) (hj : j ≠ 0) : BW := expand j hj (rescale a eP)

lemma eulerP_eq (a : PowerSeries ℚ) {j : ℕ} (hj : j ≠ 0) :
    eulerP a j hj = (1 - C a * ww ^ j) * eulerP (qq * a) j hj := by
  unfold eulerP
  conv_lhs => rw [eP_eq]
  rw [map_mul, map_mul, map_sub, map_sub, map_one, map_one, rescale_X, map_mul, expand_C,
    expand_X, rescale_rescale]

lemma coeff_eulerP (a : PowerSeries ℚ) {j : ℕ} (hj : j ≠ 0) (n : ℕ) :
    coeff n (eulerP a j hj) = if j ∣ n then a ^ (n / j) * coeff (n / j) eP else 0 := by
  rw [eulerP, coeff_expand]
  split_ifs
  · rw [coeff_rescale]
  · rfl

lemma dvd_eulerP_sub_one (M : ℕ) (b : PowerSeries ℚ) {j : ℕ} (hj : j ≠ 0) :
    C (qq ^ M) ∣ eulerP (qq ^ M * b) j hj - 1 := by
  rw [C_pow_dvd_iff]
  intro n
  rw [map_sub, coeff_eulerP, coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coeff_eP, ifac_zero]
  · rw [if_neg hn.ne', sub_zero]
    split_ifs with hjn
    · have hq : 1 ≤ n / j := Nat.div_pos (Nat.le_of_dvd hn hjn) (Nat.pos_of_ne_zero hj)
      rw [mul_pow, ← pow_mul]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow _ (by nlinarith)) _) _
    · exact dvd_zero _

/-- Euler's product formula: `(a w^j; q)_∞` is the explicit series `eulerP a j`. -/
theorem qPochInf_C_mul_pow (a : PowerSeries ℚ) {j : ℕ} (hj : j ≠ 0) :
    qPochInf (C a * ww ^ j) = eulerP a j hj := by
  set D : PowerSeries ℚ → BW := fun b => qPochInf (C b * ww ^ j) - eulerP b j hj with hD
  have hstep : ∀ b, D b = (1 - C b * ww ^ j) * D (qq * b) := by
    intro b
    simp only [hD]
    rw [qPochInf_eq, eulerP_eq b hj, map_mul, mul_assoc]
    ring
  have hiter : ∀ M N b, C (qq ^ M) ∣ D (qq ^ N * b) → C (qq ^ M) ∣ D b := by
    intro M N
    induction N with
    | zero => intro b h; simpa using h
    | succ N ih =>
        intro b h
        rw [hstep b]
        refine dvd_mul_of_dvd_right (ih (qq * b) ?_) _
        rwa [← mul_assoc, ← pow_succ]
  have hsmall : ∀ M b, C (qq ^ M) ∣ D (qq ^ M * b) := by
    intro M b
    have e : D (qq ^ M * b) =
        (qPochInf (C (qq ^ M) * (C b * ww ^ j)) - 1) - (eulerP (qq ^ M * b) j hj - 1) := by
      simp only [hD, map_mul, mul_assoc]; ring
    rw [e]
    exact dvd_sub (dvd_qPochInf_sub_one M _) (dvd_eulerP_sub_one M b hj)
  have hzero : D a = 0 := eq_zero_of_forall_dvd fun M => hiter M M a (hsmall M a)
  exact sub_eq_zero.mp hzero

lemma qPochInf_w : qPochInf ww = eP := by
  have h := qPochInf_C_mul_pow 1 one_ne_zero
  rw [map_one, one_mul, pow_one] at h
  rw [h, eulerP, rescale_one, RingHom.id_apply, expand_one_apply]

lemma qPochInf_C_mul_w (a : PowerSeries ℚ) : qPochInf (C a * ww) = rescale a eP := by
  have h := qPochInf_C_mul_pow a one_ne_zero
  rw [pow_one] at h
  rw [h, eulerP, expand_one_apply]

lemma qPochInf_C_mul_w_sq (a : PowerSeries ℚ) :
    qPochInf (C a * ww ^ 2) = expand 2 two_ne_zero (rescale a eP) :=
  qPochInf_C_mul_pow a two_ne_zero

lemma ring_inverse_eq {x y : BW} (h : x * y = 1) : Ring.inverse x = y := by
  have hu : IsUnit x := ⟨⟨x, y, h, by rw [mul_comm]; exact h⟩, rfl⟩
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [h, mul_one]
    _ = y := by rw [← mul_assoc, Ring.inverse_mul_cancel x hu, one_mul]

lemma rescale_eP_mul_eE (a : PowerSeries ℚ) : rescale a eP * rescale a eE = 1 := by
  rw [← map_mul, eP_mul_eE, map_one]

/-! ### The `t`-th summand: a finite `q`-binomial identity -/

lemma sum_range_even {M : Type*} [AddCommMonoid M] (n : ℕ) (h : ℕ → M) :
    ∑ a ∈ range (n + 1), (if 2 ∣ a then h (a / 2) else 0) =
      ∑ f ∈ range (n + 1), (if 2 * f ≤ n then h f else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have h1 : (range (n + 1)).filter (fun a => 2 ∣ a) =
      (range (n / 2 + 1)).map ⟨fun f => 2 * f, fun x y hxy => by simpa using hxy⟩ := by
    ext a
    simp only [mem_filter, mem_range, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨ha, ⟨f, rfl⟩⟩
      exact ⟨f, by omega, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨by omega, ⟨f, rfl⟩⟩
  have h2 : (range (n + 1)).filter (fun f => 2 * f ≤ n) = range (n / 2 + 1) := by
    ext f
    simp only [mem_filter, mem_range]
    omega
  rw [h1, h2, Finset.sum_map]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp

/-- `(q^t w^2; q)_∞ / (q^t w; q)_∞ = ∑_j (w;q)_j (q^t w)^j / (q;q)_j`, after Euler's formula:
the two sides agree coefficient by coefficient. -/
lemma qbinomial_w (t : ℕ) :
    expand 2 two_ne_zero (rescale (qq ^ t) eP) * rescale (qq ^ t) eE =
      wsum (fun j => C (qq ^ (t * j) * ifac j) * wPoch j) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_mul, coeff_wsum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => coeff a (expand 2 two_ne_zero (rescale (qq ^ t) eP)) *
      coeff b (rescale (qq ^ t) eE)) n]
  -- the common value
  set X : ℕ → PowerSeries ℚ := fun f =>
    (-1) ^ f * qq ^ (f.choose 2) * qq ^ (t * (n - f)) * ifac f * ifac (n - 2 * f) with hX
  have hL : ∀ a ∈ range n.succ,
      coeff a (expand 2 two_ne_zero (rescale (qq ^ t) eP)) * coeff (n - a) (rescale (qq ^ t) eE)
        = if 2 ∣ a then X (a / 2) else 0 := by
    intro a ha
    have han : a ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ha)
    rw [coeff_expand]
    split_ifs with h2
    · obtain ⟨f, rfl⟩ := h2
      rw [Nat.mul_div_cancel_left f two_pos, coeff_rescale, coeff_rescale, coeff_eP, coeff_eE]
      simp only [hX]
      have e : n - f = f + (n - 2 * f) := by omega
      rw [e, mul_add, pow_add, ← pow_mul, ← pow_mul]
      ring
    · rw [zero_mul]
  rw [Finset.sum_congr rfl hL, sum_range_even]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hfn : f ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hf)
  have e1 : n + 1 - 1 - f = n - f := by omega
  rw [e1, coeff_C_mul, coeff_wPoch, show n - (n - f) = f by omega]
  split_ifs with h2f
  · simp only [hX]
    rw [show qq ^ (t * (n - f)) * ifac (n - f) * (gaussBinom qq (n - f) f * (-1) ^ f *
        qq ^ f.choose 2) = qq ^ (t * (n - f)) * (-1) ^ f * qq ^ f.choose 2 *
        (ifac (n - f) * gaussBinom qq (n - f) f) by ring,
      ifac_mul_gaussBinom (by omega), show n - f - f = n - 2 * f by omega]
    ring
  · rw [ErdosProblems.Erdos1049.gaussBinom_eq_zero_of_lt qq (by omega)]
    ring

/-- `E(w) (q^t w^2;q)_∞/(q^t w;q)_∞ = ∑_j q^{tj} w^j/(q;q)_j · E(q^j w)`. -/
lemma eE_mul_qbinomial_w (t : ℕ) :
    eE * (expand 2 two_ne_zero (rescale (qq ^ t) eP) * rescale (qq ^ t) eE) =
      wsum (fun j => C (qq ^ (t * j) * ifac j) * rescale (qq ^ j) eE) := by
  rw [qbinomial_w, mul_wsum]
  refine wsum_congr fun j => ?_
  rw [mul_left_comm, eE_mul_wPoch]

/-- `∑_j q^{tj} w^j/(q;q)_j E(q^j w) = ∑_d w^d/(q;q)_d E(q^{t+d} w)`. -/
lemma wsum_shift (t : ℕ) :
    wsum (fun j => C (qq ^ (t * j) * ifac j) * rescale (qq ^ j) eE) =
      wsum (fun d => C (ifac d) * rescale (qq ^ (t + d)) eE) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_wsum, coeff_wsum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show n + 1 - 1 - j = n - j by omega, show n - (n - j) = j by omega, coeff_C_mul,
    coeff_C_mul, coeff_rescale, coeff_rescale, coeff_eE, coeff_eE, ← pow_mul, ← pow_mul,
    show (t + j) * (n - j) = t * (n - j) + (n - j) * j by ring, pow_add]
  ring

/-! ### The paper's objects -/

/-- The generating function
`G_q(w) = (w;q)_∞^{-3} ∑_{t ≥ 0} w^t/(q;q)_t · (q^t w^2;q)_∞ / (q^t w;q)_∞^2`
in `ℚ⟦q⟧⟦w⟧`, with the infinite products taken in the product topology. -/
def momentGenFun : BW :=
  Ring.inverse (qPochInf ww ^ 3) *
    ∑' t : ℕ, ww ^ t * C (qfac t)⁻¹ *
      (qPochInf (C (qq ^ t) * ww ^ 2) * Ring.inverse (qPochInf (C (qq ^ t) * ww) ^ 2))

/-- The moment weight `γ_k(q) = [w^k] G_q(w) ∈ ℚ⟦q⟧`. -/
def momentWeight (k : ℕ) : PowerSeries ℚ := coeff k momentGenFun

/-- `R_k^{(r)}(q) = ∑_{n_1+⋯+n_r=k} (q;q)_k / ∏_{j ≤ r} (q;q)_{n_j}`, the sum over compositions
of `k` into `r` nonnegative parts. -/
def rogersR (r k : ℕ) : PowerSeries ℚ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, qfac k * (∏ j, qfac (n j))⁻¹

/-! ### `G_q` in explicit form -/

lemma momentGenFun_eq :
    momentGenFun = eE ^ 2 * wsum (fun t => wsum (fun d =>
      C (ifac t * ifac d) * (rescale (qq ^ (t + d)) eE * rescale (qq ^ t) eE))) := by
  have hinv3 : Ring.inverse (qPochInf ww ^ 3) = eE ^ 3 := by
    rw [qPochInf_w]
    apply ring_inverse_eq
    rw [← mul_pow, eP_mul_eE, one_pow]
  have hinv2 : ∀ t : ℕ, Ring.inverse (qPochInf (C (qq ^ t) * ww) ^ 2) =
      rescale (qq ^ t) eE ^ 2 := by
    intro t
    rw [qPochInf_C_mul_w]
    apply ring_inverse_eq
    rw [← mul_pow, rescale_eP_mul_eE, one_pow]
  have hterm : (fun t : ℕ => ww ^ t * C (qfac t)⁻¹ *
      (qPochInf (C (qq ^ t) * ww ^ 2) * Ring.inverse (qPochInf (C (qq ^ t) * ww) ^ 2))) =
      fun t => ww ^ t * (C (ifac t) * ((expand 2 two_ne_zero (rescale (qq ^ t) eP) *
        rescale (qq ^ t) eE) * rescale (qq ^ t) eE)) := by
    funext t
    rw [qPochInf_C_mul_w_sq, hinv2, ifac]
    ring
  rw [momentGenFun, hinv3, hterm, (hasSum_wsum _).tsum_eq,
    show eE ^ 3 = eE ^ 2 * eE by ring, mul_assoc, mul_wsum]
  congr 1
  refine wsum_congr fun t => ?_
  rw [show eE * (C (ifac t) * ((expand 2 two_ne_zero (rescale (qq ^ t) eP) *
      rescale (qq ^ t) eE) * rescale (qq ^ t) eE)) =
      C (ifac t) * ((eE * (expand 2 two_ne_zero (rescale (qq ^ t) eP) *
      rescale (qq ^ t) eE)) * rescale (qq ^ t) eE) by ring,
    eE_mul_qbinomial_w, wsum_shift, wsum_mul, mul_wsum]
  refine wsum_congr fun d => ?_
  rw [map_mul]
  ring

/-! ### The `q`-derivative and the `q`-Leibniz rule -/

/-- The `q`-derivative `(∂_q f)(w) = (f(w) - f(qw))/w`. -/
def qD (f : BW) : BW := mk fun n => (1 - qq ^ (n + 1)) * coeff (n + 1) f

lemma coeff_qD (f : BW) (n : ℕ) : coeff n (qD f) = (1 - qq ^ (n + 1)) * coeff (n + 1) f :=
  coeff_mk _ _

lemma qD_add (f g : BW) : qD (f + g) = qD f + qD g := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_qD, map_add]; ring

lemma qD_C_mul (c : PowerSeries ℚ) (f : BW) : qD (C c * f) = C c * qD f := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_qD, coeff_C_mul]; ring

lemma qD_zero : qD 0 = 0 := by
  refine PowerSeries.ext fun n => ?_
  simp [coeff_qD]

lemma qD_sum {ι : Type*} (s : Finset ι) (F : ι → BW) : qD (∑ i ∈ s, F i) = ∑ i ∈ s, qD (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qD_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qD_add, ih]

lemma qD_mul (f g : BW) : qD (f * g) = qD f * g + rescale qq f * qD g := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_qD, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum]
  have hsplit : ∀ p ∈ antidiagonal (n + 1),
      (1 - qq ^ (n + 1)) * (coeff p.1 f * coeff p.2 g) =
        (1 - qq ^ p.1) * coeff p.1 f * coeff p.2 g +
          qq ^ p.1 * coeff p.1 f * ((1 - qq ^ p.2) * coeff p.2 g) := by
    intro p hp
    rw [mem_antidiagonal] at hp
    rw [← hp, pow_add]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [pow_zero, sub_self, zero_mul, zero_add, coeff_qD]
  · rw [Finset.Nat.sum_antidiagonal_succ']
    simp only [pow_zero, sub_self, zero_mul, mul_zero, zero_add, coeff_qD, coeff_rescale]

lemma qD_rescale (a : PowerSeries ℚ) (f : BW) : qD (rescale a f) = C a * rescale a (qD f) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_qD, coeff_C_mul, coeff_rescale, coeff_rescale, coeff_qD, pow_succ]
  ring

lemma qD_eE : qD eE = eE := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_qD, coeff_eE, coeff_eE, ifac_succ n]
  ring

lemma qD_iter_eE (r : ℕ) : qD^[r] eE = eE := Function.iterate_fixed qD_eE r

lemma coeff_qD_iter (f : BW) (r m : ℕ) :
    coeff m (qD^[r] f) = qfac (m + r) * ifac m * coeff (m + r) f := by
  induction r generalizing m with
  | zero =>
      rw [Function.iterate_zero_apply, Nat.add_zero, qfac_mul_ifac, one_mul]
  | succ r ih =>
      rw [Function.iterate_succ_apply', coeff_qD, ih, ifac_succ m,
        show m + 1 + r = m + (r + 1) by omega]
      ring

/-- The `q`-Leibniz rule for a product with `E(w) = 1/(w;q)_∞`:
`∂_q^r (E g) = ∑_l [r,l]_q E(q^{r-l} w) ∂_q^{r-l} g`. -/
lemma qD_iter_eE_mul (g : BW) (r : ℕ) :
    qD^[r] (eE * g) = ∑ l ∈ range (r + 1),
      C (gaussBinom qq r l) * (rescale (qq ^ (r - l)) eE * qD^[r - l] g) := by
  induction r with
  | zero =>
      simp [ErdosProblems.Erdos1049.gaussBinom_zero_right]
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, qD_sum]
      -- derivative of each summand
      have hder : ∀ l ∈ range (r + 1),
          qD (C (gaussBinom qq r l) * (rescale (qq ^ (r - l)) eE * qD^[r - l] g)) =
            C (qq ^ (r - l) * gaussBinom qq r l) *
                (rescale (qq ^ (r - l)) eE * qD^[r - l] g) +
              C (gaussBinom qq r l) *
                (rescale (qq ^ (r - l + 1)) eE * qD^[r - l + 1] g) := by
        intro l _
        rw [qD_C_mul, qD_mul, qD_rescale, qD_eE, rescale_rescale, ← pow_succ,
          ← Function.iterate_succ_apply' qD, map_mul]
        ring
      rw [Finset.sum_congr rfl hder, Finset.sum_add_distrib]
      -- the target, split at `l = 0`
      rw [Finset.sum_range_succ' (fun l => C (gaussBinom qq (r + 1) l) *
        (rescale (qq ^ (r + 1 - l)) eE * qD^[r + 1 - l] g))]
      have hpascal : ∀ l ∈ range (r + 1),
          C (gaussBinom qq (r + 1) (l + 1)) *
              (rescale (qq ^ (r + 1 - (l + 1))) eE * qD^[r + 1 - (l + 1)] g) =
            C (gaussBinom qq r (l + 1)) * (rescale (qq ^ (r - l)) eE * qD^[r - l] g) +
              C (qq ^ (r - l) * gaussBinom qq r l) *
                (rescale (qq ^ (r - l)) eE * qD^[r - l] g) := by
        intro l hl
        have hlr : l ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hl)
        rw [ErdosProblems.Erdos1049.gaussBinom_succ_of_le qq hlr, map_add,
          show r + 1 - (l + 1) = r - l by omega]
        ring
      rw [Finset.sum_congr rfl hpascal, Finset.sum_add_distrib]
      -- the second half of the derivative, split at `l = 0`
      rw [Finset.sum_range_succ' (fun l => C (gaussBinom qq r l) *
        (rescale (qq ^ (r - l + 1)) eE * qD^[r - l + 1] g))]
      have hshift : ∀ l ∈ range r,
          C (gaussBinom qq r (l + 1)) *
              (rescale (qq ^ (r - (l + 1) + 1)) eE * qD^[r - (l + 1) + 1] g) =
            C (gaussBinom qq r (l + 1)) * (rescale (qq ^ (r - l)) eE * qD^[r - l] g) := by
        intro l hl
        have hlr : l < r := mem_range.mp hl
        rw [show r - (l + 1) + 1 = r - l by omega]
      rw [Finset.sum_congr rfl hshift]
      rw [Finset.sum_range_succ (fun l => C (gaussBinom qq r (l + 1)) *
        (rescale (qq ^ (r - l)) eE * qD^[r - l] g)),
        ErdosProblems.Erdos1049.gaussBinom_eq_zero_of_lt qq (Nat.lt_succ_self r)]
      simp only [ErdosProblems.Erdos1049.gaussBinom_zero_right, map_zero, zero_mul, add_zero,
        Nat.sub_zero, map_one, one_mul]
      ring

/-! ### The Rogers sums -/

lemma sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (k n : ℕ)
    (f : (Fin (k + 1) → ℕ) → M) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple (k + 1) n, f x =
      ∑ p ∈ antidiagonal n, ∑ y ∈ Finset.Nat.antidiagonalTuple k p.2, f (Fin.cons p.1 y) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => (⟨(x 0, n - x 0), Fin.tail x⟩ : Σ _ : ℕ × ℕ, Fin k → ℕ))
    (fun py _ => Fin.cons py.1.1 py.2) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hx
    simp only [mem_sigma, mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨by omega, ?_⟩
    simp only [Fin.tail]
    omega
  · intro py hpy
    simp only [mem_sigma, mem_antidiagonal, Finset.Nat.mem_antidiagonalTuple] at hpy
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega
  · intro x _
    exact Fin.cons_self_tail x
  · intro py hpy
    simp only [mem_sigma, mem_antidiagonal] at hpy
    obtain ⟨⟨a, b⟩, y⟩ := py
    simp only at hpy
    have hb : n - a = b := by omega
    simp only [Fin.cons_zero, Fin.tail_cons, hb]
  · intro x _
    rw [Fin.cons_self_tail]

lemma sum_antidiagonalTuple_two {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (Fin 2 → ℕ) → M) :
    ∑ x ∈ Finset.Nat.antidiagonalTuple 2 n, f x = ∑ p ∈ antidiagonal n, f ![p.1, p.2] := by
  rw [Finset.Nat.antidiagonalTuple_two, Finset.sum_map]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1

lemma inv_qfac_mul (a b : ℕ) : (qfac a * qfac b)⁻¹ = ifac a * ifac b := by
  rw [PowerSeries.mul_inv_rev, ifac, ifac, mul_comm]

lemma rogersR_two (n : ℕ) :
    rogersR 2 n = ∑ r ∈ range (n + 1), qfac n * ifac r * ifac (n - r) := by
  rw [rogersR, sum_antidiagonalTuple_two, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [inv_qfac_mul, mul_assoc]

lemma coeff_eE_cube (n : ℕ) : coeff n (eE * (eE * eE)) = rogersR 3 n * ifac n := by
  rw [rogersR, Finset.sum_mul, sum_antidiagonalTuple_succ, coeff_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeff_mul, coeff_eE, Finset.mul_sum, sum_antidiagonalTuple_two]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coeff_eE, coeff_eE, Fin.prod_univ_succ, Fin.prod_univ_two]
  simp only [Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [PowerSeries.mul_inv_rev, inv_qfac_mul, ← ifac]
  linear_combination (-(ifac q.1 * ifac q.2 * ifac p.1)) * qfac_mul_ifac n

/-! ### The factorisation -/

/-- `∑_k R_k^{(2)} R_k^{(3)} / (q;q)_k · w^k`. -/
def rogersSeries : BW := mk fun n => rogersR 2 n * rogersR 3 n * ifac n

lemma rogersSeries_eq_wsum :
    rogersSeries = wsum (fun r => C (ifac r) * qD^[r] (eE * (eE * eE))) := by
  refine PowerSeries.ext fun n => ?_
  rw [rogersSeries, coeff_mk, coeff_wsum, rogersR_two, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
  rw [coeff_C_mul, coeff_qD_iter, show n - r + r = n by omega, coeff_eE_cube]
  ring

lemma rogersSeries_eq : rogersSeries = eE ^ 2 * wsum (fun u => wsum (fun v =>
    C (ifac u * ifac v) * (rescale (qq ^ (u + v)) eE * rescale (qq ^ v) eE))) := by
  have h1 : ∀ r, C (ifac r) * qD^[r] (eE * (eE * eE)) =
      ∑ p ∈ antidiagonal r, C (ifac p.1) * (C (ifac p.2) *
        (rescale (qq ^ p.2) eE * qD^[p.2] (eE * eE))) := by
    intro r
    rw [qD_iter_eE_mul, Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun l s => C (ifac l) * (C (ifac s) * (rescale (qq ^ s) eE * qD^[s] (eE * eE))))]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlr : l ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hl)
    rw [← mul_assoc, ← map_mul, ifac_mul_gaussBinom hlr, map_mul]
    ring
  have h3 : ∀ s, C (ifac s) * (rescale (qq ^ s) eE * qD^[s] (eE * eE)) =
      ∑ p ∈ antidiagonal s, C (ifac p.1 * ifac p.2) *
        (rescale (qq ^ (p.1 + p.2)) eE * rescale (qq ^ p.2) eE) * eE := by
    intro s
    rw [qD_iter_eE_mul, Finset.mul_sum, Finset.mul_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => C (ifac u * ifac v) *
        (rescale (qq ^ (u + v)) eE * rescale (qq ^ v) eE) * eE)]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hus : u ≤ s := Nat.lt_succ_iff.mp (mem_range.mp hu)
    rw [qD_iter_eE, show u + (s - u) = s by omega, ← ifac_mul_gaussBinom hus, map_mul]
    ring
  calc rogersSeries
      = wsum (fun r => C (ifac r) * qD^[r] (eE * (eE * eE))) := rogersSeries_eq_wsum
    _ = wsum (fun r => ∑ p ∈ antidiagonal r, C (ifac p.1) * (C (ifac p.2) *
          (rescale (qq ^ p.2) eE * qD^[p.2] (eE * eE)))) := wsum_congr h1
    _ = wsum (fun l => wsum (fun s => C (ifac l) * (C (ifac s) *
          (rescale (qq ^ s) eE * qD^[s] (eE * eE))))) :=
        wsum_antidiag (fun l s => C (ifac l) * (C (ifac s) *
          (rescale (qq ^ s) eE * qD^[s] (eE * eE))))
    _ = wsum (fun l => C (ifac l) * wsum (fun s => C (ifac s) *
          (rescale (qq ^ s) eE * qD^[s] (eE * eE)))) :=
        wsum_congr fun l => (mul_wsum _ _).symm
    _ = eE * wsum (fun s => C (ifac s) * (rescale (qq ^ s) eE * qD^[s] (eE * eE))) :=
        wsum_C_mul ifac _
    _ = eE * wsum (fun s => ∑ p ∈ antidiagonal s, C (ifac p.1 * ifac p.2) *
          (rescale (qq ^ (p.1 + p.2)) eE * rescale (qq ^ p.2) eE) * eE) := by
        rw [wsum_congr h3]
    _ = eE * wsum (fun u => wsum (fun v => C (ifac u * ifac v) *
          (rescale (qq ^ (u + v)) eE * rescale (qq ^ v) eE) * eE)) := by
        congr 1
        exact wsum_antidiag (fun u v => C (ifac u * ifac v) *
          (rescale (qq ^ (u + v)) eE * rescale (qq ^ v) eE) * eE)
    _ = eE * wsum (fun u => wsum (fun v => C (ifac u * ifac v) *
          (rescale (qq ^ (u + v)) eE * rescale (qq ^ v) eE)) * eE) := by
        congr 1
        exact wsum_congr fun u => (wsum_mul _ _).symm
    _ = eE * (wsum (fun u => wsum (fun v => C (ifac u * ifac v) *
          (rescale (qq ^ (u + v)) eE * rescale (qq ^ v) eE))) * eE) := by
        congr 1
        exact (wsum_mul _ _).symm
    _ = eE ^ 2 * wsum (fun u => wsum (fun v =>
          C (ifac u * ifac v) * (rescale (qq ^ (u + v)) eE * rescale (qq ^ v) eE))) := by
        ring

theorem momentGenFun_eq_rogersSeries : momentGenFun = rogersSeries := by
  rw [momentGenFun_eq, rogersSeries_eq]
  refine congrArg (fun X => eE ^ 2 * X) ?_
  refine (wsum_comm (fun t d =>
    C (ifac t * ifac d) * (rescale (qq ^ (t + d)) eE * rescale (qq ^ t) eE))).trans ?_
  refine wsum_congr fun d => wsum_congr fun t => ?_
  rw [mul_comm (ifac t) (ifac d), add_comm t d]

theorem momentWeight_eq (k : ℕ) :
    momentWeight k = rogersR 2 k * rogersR 3 k * (qfac k)⁻¹ := by
  rw [momentWeight, momentGenFun_eq_rogersSeries, rogersSeries, coeff_mk, ifac]

/-! ### `R_k^{(2)} R_k^{(3)}` as a polynomial with nonnegative integer coefficients -/

/-- `R_k^{(2)}` as an integer polynomial, `∑_i [k, i]_q`. -/
def rogersPoly2 (k : ℕ) : Polynomial ℤ := ∑ i ∈ range (k + 1), gaussBinom Polynomial.X k i

/-- `R_k^{(3)}` as an integer polynomial, `∑_{a+m=k} ∑_{b+c=m} [k, a]_q [m, b]_q`. -/
def rogersPoly3 (k : ℕ) : Polynomial ℤ :=
  ∑ p ∈ antidiagonal k, ∑ q ∈ antidiagonal p.2,
    gaussBinom Polynomial.X k p.1 * gaussBinom Polynomial.X p.2 q.1

/-- The embedding `ℤ[q] → ℚ⟦q⟧`. -/
def toQSeries : Polynomial ℤ →+* PowerSeries ℚ :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

lemma toQSeries_apply (f : Polynomial ℤ) :
    toQSeries f = ((f.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := rfl

lemma toQSeries_X : toQSeries Polynomial.X = qq := by
  rw [toQSeries_apply, Polynomial.map_X, Polynomial.coe_X]

lemma toQSeries_gaussBinom (n k : ℕ) :
    toQSeries (gaussBinom Polynomial.X n k) = gaussBinom qq n k := by
  rw [map_gaussBinom, toQSeries_X]

lemma toQSeries_rogersPoly2 (k : ℕ) : toQSeries (rogersPoly2 k) = rogersR 2 k := by
  rw [rogersPoly2, map_sum, rogersR_two]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [toQSeries_gaussBinom, gaussBinom_eq (Nat.lt_succ_iff.mp (mem_range.mp hi))]

lemma rogersR_three (k : ℕ) :
    rogersR 3 k = ∑ p ∈ antidiagonal k, ∑ q ∈ antidiagonal p.2,
      qfac k * ifac p.1 * ifac q.1 * ifac q.2 := by
  rw [rogersR, sum_antidiagonalTuple_succ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_antidiagonalTuple_two]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Fin.prod_univ_succ, Fin.prod_univ_two]
  simp only [Fin.cons_zero, Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [PowerSeries.mul_inv_rev, inv_qfac_mul, ← ifac]
  ring

lemma toQSeries_rogersPoly3 (k : ℕ) : toQSeries (rogersPoly3 k) = rogersR 3 k := by
  rw [rogersPoly3, rogersR_three, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mem_antidiagonal] at hp hq
  rw [map_mul, toQSeries_gaussBinom, toQSeries_gaussBinom, gaussBinom_eq (by omega : p.1 ≤ k),
    gaussBinom_eq (by omega : q.1 ≤ p.2), show k - p.1 = p.2 by omega,
    show p.2 - q.1 = q.2 by omega]
  linear_combination (qfac k * ifac p.1 * ifac q.1 * ifac q.2) * qfac_mul_ifac p.2

open Polynomial in
lemma coeff_nonneg_mul {f g : Polynomial ℤ} (hf : ∀ n, 0 ≤ f.coeff n) (hg : ∀ n, 0 ≤ g.coeff n)
    (n : ℕ) : 0 ≤ (f * g).coeff n := by
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

open Polynomial in
lemma coeff_nonneg_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ)
    (h : ∀ i ∈ s, ∀ n, 0 ≤ (f i).coeff n) (n : ℕ) : 0 ≤ (∑ i ∈ s, f i).coeff n := by
  rw [finset_sum_coeff]
  exact Finset.sum_nonneg fun i hi => h i hi n

lemma gaussBinom_coeff_nonneg (n k d : ℕ) : 0 ≤ (gaussBinom (Polynomial.X : Polynomial ℤ) n k).coeff d :=
  (ErdosProblems.Erdos1049.PaperR11.gaussian_coefficient_bounds n k d).1

lemma rogersPoly2_coeff_nonneg (k n : ℕ) : 0 ≤ (rogersPoly2 k).coeff n :=
  coeff_nonneg_sum _ _ (fun i _ d => gaussBinom_coeff_nonneg k i d) n

lemma rogersPoly3_coeff_nonneg (k n : ℕ) : 0 ≤ (rogersPoly3 k).coeff n :=
  coeff_nonneg_sum _ _ (fun _ _ => coeff_nonneg_sum _ _ (fun _ _ =>
    coeff_nonneg_mul (gaussBinom_coeff_nonneg _ _) (gaussBinom_coeff_nonneg _ _))) n

open Polynomial in
/-- The degree of a sum of polynomials with nonnegative coefficients is attained by a monic
summand of maximal degree: no cancellation occurs. -/
lemma natDegree_sum_of_nonneg {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ) (D : ℕ)
    (hnn : ∀ i ∈ s, ∀ n, 0 ≤ (f i).coeff n) (hle : ∀ i ∈ s, (f i).natDegree ≤ D)
    (i0 : ι) (hi0 : i0 ∈ s) (hmon : (f i0).Monic) (hdeg : (f i0).natDegree = D) :
    (∑ i ∈ s, f i).natDegree = D := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [finset_sum_coeff]
    exact Finset.sum_eq_zero fun i hi => coeff_eq_zero_of_natDegree_lt ((hle i hi).trans_lt hN)
  · apply le_natDegree_of_ne_zero
    rw [finset_sum_coeff]
    have h1 : (f i0).coeff D = 1 := by rw [← hdeg]; exact hmon.leadingCoeff
    have h2 : (f i0).coeff D ≤ ∑ i ∈ s, (f i).coeff D :=
      Finset.single_le_sum (fun i hi => hnn i hi D) hi0
    omega

lemma mul_sub_le_sq_div_four (k i : ℕ) (hi : i ≤ k) : i * (k - i) ≤ k ^ 2 / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_sub_cancel_left]
  nlinarith [sq_nonneg ((i : ℤ) - j), Nat.zero_le i, Nat.zero_le j]

lemma half_mul_sub_half (k : ℕ) : k / 2 * (k - k / 2) = k ^ 2 / 4 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [show 2 * m / 2 = m by omega, show 2 * m - m = m by omega,
      show (2 * m) ^ 2 = 4 * (m * m) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  · rw [show (2 * m + 1) / 2 = m by omega, show 2 * m + 1 - m = m + 1 by omega,
      show (2 * m + 1) ^ 2 = 1 + 4 * (m * (m + 1)) by ring,
      Nat.add_mul_div_left _ _ (by norm_num)]
    norm_num

lemma rogersPoly2_natDegree (k : ℕ) : (rogersPoly2 k).natDegree = k ^ 2 / 4 := by
  apply natDegree_sum_of_nonneg _ _ _ (fun i _ d => gaussBinom_coeff_nonneg k i d)
    _ (k / 2) (mem_range.mpr (by omega))
    (ErdosProblems.Erdos1049.PaperR12.gaussian_polynomial_monic k (k / 2) (by omega))
  · rw [ErdosProblems.Erdos1049.PaperR12.gaussian_polynomial_natDegree k (k / 2) (by omega)]
    exact half_mul_sub_half k
  · intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [ErdosProblems.Erdos1049.PaperR12.gaussian_polynomial_natDegree k i hik]
    exact mul_sub_le_sq_div_four k i hik

lemma three_mul_le_sq (a b c : ℕ) : a * (b + c) + b * c ≤ (a + b + c) ^ 2 / 3 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith [sq_nonneg ((a : ℤ) - b), sq_nonneg ((b : ℤ) - c), sq_nonneg ((a : ℤ) - c)]

lemma balanced_triple (k : ℕ) :
    k / 3 * (k - k / 3) + (k + 1) / 3 * (k - k / 3 - (k + 1) / 3) = k ^ 2 / 3 := by
  obtain ⟨t, rfl | rfl | rfl⟩ : ∃ t, k = 3 * t ∨ k = 3 * t + 1 ∨ k = 3 * t + 2 :=
    ⟨k / 3, by omega⟩
  · rw [show 3 * t / 3 = t by omega, show (3 * t + 1) / 3 = t by omega,
      show 3 * t - t = 2 * t by omega, show 2 * t - t = t by omega,
      show (3 * t) ^ 2 = 3 * (3 * t * t) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    ring
  · rw [show (3 * t + 1) / 3 = t by omega, show (3 * t + 1 + 1) / 3 = t by omega,
      show 3 * t + 1 - t = 2 * t + 1 by omega, show 2 * t + 1 - t = t + 1 by omega,
      show (3 * t + 1) ^ 2 = 1 + 3 * (3 * t * t + 2 * t) by ring,
      Nat.add_mul_div_left _ _ (by norm_num)]
    norm_num
    ring
  · rw [show (3 * t + 2) / 3 = t by omega, show (3 * t + 2 + 1) / 3 = t + 1 by omega,
      show 3 * t + 2 - t = 2 * t + 2 by omega, show 2 * t + 2 - (t + 1) = t + 1 by omega,
      show (3 * t + 2) ^ 2 = 1 + 3 * (3 * t * t + 4 * t + 1) by ring,
      Nat.add_mul_div_left _ _ (by norm_num)]
    norm_num
    ring

lemma rogersPoly3_natDegree (k : ℕ) : (rogersPoly3 k).natDegree = k ^ 2 / 3 := by
  rw [rogersPoly3, Finset.sum_sigma']
  have hmon : ∀ x ∈ (antidiagonal k).sigma (fun p : ℕ × ℕ => antidiagonal p.2),
      (gaussBinom (Polynomial.X : Polynomial ℤ) k x.1.1 * gaussBinom Polynomial.X x.1.2 x.2.1).Monic ∧
      (gaussBinom (Polynomial.X : Polynomial ℤ) k x.1.1 * gaussBinom Polynomial.X x.1.2 x.2.1).natDegree
        = x.1.1 * (x.2.1 + x.2.2) + x.2.1 * x.2.2 := by
    intro x hx
    simp only [mem_sigma, mem_antidiagonal] at hx
    obtain ⟨h1, h2⟩ := hx
    have m1 := ErdosProblems.Erdos1049.PaperR12.gaussian_monic_natDegree k x.1.1 (by omega)
    have m2 := ErdosProblems.Erdos1049.PaperR12.gaussian_monic_natDegree x.1.2 x.2.1 (by omega)
    refine ⟨m1.1.mul m2.1, ?_⟩
    rw [m1.1.natDegree_mul m2.1, m1.2, m2.2, show k - x.1.1 = x.2.1 + x.2.2 by omega,
      show x.1.2 - x.2.1 = x.2.2 by omega]
  have hx0 : (⟨(k / 3, k - k / 3), ((k + 1) / 3, k - k / 3 - (k + 1) / 3)⟩ :
      Σ _ : ℕ × ℕ, ℕ × ℕ) ∈ (antidiagonal k).sigma (fun p : ℕ × ℕ => antidiagonal p.2) := by
    simp only [mem_sigma, mem_antidiagonal]
    omega
  refine natDegree_sum_of_nonneg _ (fun x : (Σ _ : ℕ × ℕ, ℕ × ℕ) =>
      gaussBinom Polynomial.X k x.1.1 * gaussBinom Polynomial.X x.1.2 x.2.1) (k ^ 2 / 3)
    (fun x _ d => coeff_nonneg_mul (gaussBinom_coeff_nonneg _ _) (gaussBinom_coeff_nonneg _ _) d)
    ?_ _ hx0 (hmon _ hx0).1 ?_
  · intro x hx
    rw [(hmon x hx).2]
    simp only [mem_sigma, mem_antidiagonal] at hx
    have hk : k = x.1.1 + x.2.1 + x.2.2 := by omega
    rw [hk]
    exact three_mul_le_sq _ _ _
  · rw [(hmon _ hx0).2]
    dsimp only
    rw [show (k + 1) / 3 + (k - k / 3 - (k + 1) / 3) = k - k / 3 by omega]
    exact balanced_triple k

lemma eval_one_gaussBinom (n k : ℕ) :
    (gaussBinom (Polynomial.X : Polynomial ℤ) n k).eval 1 = (n.choose k : ℤ) := by
  have h := map_gaussBinom (Polynomial.evalRingHom (1 : ℤ)) Polynomial.X n k
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_X] at h
  rw [h, ErdosProblems.Erdos1049.PaperR12.gaussian_at_one]

lemma rogersPoly2_eval_one (k : ℕ) : (rogersPoly2 k).eval 1 = 2 ^ k := by
  rw [rogersPoly2, Polynomial.eval_finset_sum]
  simp_rw [eval_one_gaussBinom]
  exact_mod_cast Nat.sum_range_choose k

lemma rogersPoly3_eval_one (k : ℕ) : (rogersPoly3 k).eval 1 = 3 ^ k := by
  rw [rogersPoly3, Polynomial.eval_finset_sum]
  have hinner : ∀ p ∈ antidiagonal k, (∑ q ∈ antidiagonal p.2,
      gaussBinom (Polynomial.X : Polynomial ℤ) k p.1 * gaussBinom Polynomial.X p.2 q.1).eval 1 =
      (k.choose p.1 : ℤ) * 2 ^ p.2 := by
    intro p _
    rw [Polynomial.eval_finset_sum]
    simp_rw [Polynomial.eval_mul, eval_one_gaussBinom]
    rw [← Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 1
    exact_mod_cast Nat.sum_range_choose p.2
  rw [Finset.sum_congr rfl hinner, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h3 := add_pow (1 : ℤ) 2 k
  rw [show (1 : ℤ) + 2 = 3 by norm_num] at h3
  rw [h3]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [one_pow, one_mul, mul_comm]

lemma coefficientQFactorialPoly_succ (n : ℕ) :
    ErdosProblems.Erdos1049.PaperR20.coefficientQFactorialPoly (n + 1) =
      ErdosProblems.Erdos1049.PaperR20.coefficientQFactorialPoly n *
        ∑ i ∈ range (n + 1), (Polynomial.X : Polynomial ℤ) ^ i := by
  rw [ErdosProblems.Erdos1049.PaperR20.coefficientQFactorialPoly,
    ErdosProblems.Erdos1049.PaperR20.coefficientQFactorialPoly, Finset.prod_range_succ]

/-- `(q;q)_n = (1 - q)^n [n]_q!`: the tree's `coefficientQFactorialPoly` is the `q`-factorial,
not the `q`-Pochhammer `(q;q)_n` of the proposition. -/
lemma qfac_eq_coefficientQFactorialPoly (n : ℕ) :
    qfac n = (1 - qq) ^ n *
      toQSeries (ErdosProblems.Erdos1049.PaperR20.coefficientQFactorialPoly n) := by
  induction n with
  | zero =>
      rw [ErdosProblems.Erdos1049.PaperR20.coefficientQFactorialPoly_zero, map_one, pow_zero,
        one_mul, qfac_zero]
  | succ n ih =>
      have hgeom : (1 - qq) * ∑ i ∈ range (n + 1), toQSeries (Polynomial.X ^ i) =
          1 - qq ^ (n + 1) := by
        simp only [map_pow, toQSeries_X]
        rw [mul_comm, geom_sum_mul_neg]
      rw [qfac_succ, ih, coefficientQFactorialPoly_succ, map_mul, map_sum, ← hgeom,
        pow_succ (1 - qq) n]
      ring

/-- `long1049:prop:rogers-factorisation`: the moment weights as a product of two finite sums.

Here `q` is an indeterminate: `γ_k(q) = [w^k] G_q(w)` is computed in `ℚ⟦q⟧⟦w⟧` from
`G_q(w) = (w;q)_∞^{-3} ∑_{t ≥ 0} w^t/(q;q)_t · (q^t w^2;q)_∞/(q^t w;q)_∞^2`, the infinite
products being genuine infinite products in the product topology, and
`R_k^{(r)}(q) = ∑_{n_1+⋯+n_r=k} (q;q)_k / ∏_{j ≤ r} (q;q)_{n_j}`.  Then

* `γ_k(q) = R_k^{(2)}(q) R_k^{(3)}(q) / (q;q)_k` (equivalently
  `(q;q)_k γ_k(q) = R_k^{(2)}(q) R_k^{(3)}(q)`);
* the product `R_k^{(2)} R_k^{(3)}` lies in `ℤ_{≥0}[q]`: it is the image of a polynomial
  `p ∈ ℕ[q]`, which has degree `⌊k²/4⌋ + ⌊k²/3⌋` and coefficient sum `p(1) = 6^k`;
* consequently `(q;q)_k γ_k ∈ ℤ[q]`. -/
theorem rogers_factorisation (k : ℕ) :
    momentWeight k = rogersR 2 k * rogersR 3 k * (qfac k)⁻¹ ∧
    qfac k * momentWeight k = rogersR 2 k * rogersR 3 k ∧
    (∃ p : Polynomial ℕ,
      ((p.map (Nat.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) = rogersR 2 k * rogersR 3 k ∧
      p.natDegree = k ^ 2 / 4 + k ^ 2 / 3 ∧
      p.eval 1 = 6 ^ k) ∧
    (∃ g : Polynomial ℤ,
      qfac k * momentWeight k = ((g.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)) := by
  have hγ := momentWeight_eq k
  have hmul : qfac k * momentWeight k = rogersR 2 k * rogersR 3 k := by
    rw [hγ, ← ifac]
    linear_combination (rogersR 2 k * rogersR 3 k) * qfac_mul_ifac k
  have hfq : toQSeries (rogersPoly2 k * rogersPoly3 k) = rogersR 2 k * rogersR 3 k := by
    rw [map_mul, toQSeries_rogersPoly2, toQSeries_rogersPoly3]
  have hnn : ∀ n, 0 ≤ (rogersPoly2 k * rogersPoly3 k).coeff n :=
    coeff_nonneg_mul (rogersPoly2_coeff_nonneg k) (rogersPoly3_coeff_nonneg k)
  have hlift : rogersPoly2 k * rogersPoly3 k ∈ Polynomial.lifts (Nat.castRingHom ℤ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨((rogersPoly2 k * rogersPoly3 k).coeff n).toNat, by simp [Int.toNat_of_nonneg (hnn n)]⟩
  obtain ⟨p, hp⟩ := (Polynomial.mem_lifts _).mp hlift
  have h2ne : rogersPoly2 k ≠ 0 := fun h => by
    have := rogersPoly2_eval_one k
    rw [h, Polynomial.eval_zero] at this
    exact (pow_ne_zero k (by norm_num : (2 : ℤ) ≠ 0)) this.symm
  have h3ne : rogersPoly3 k ≠ 0 := fun h => by
    have := rogersPoly3_eval_one k
    rw [h, Polynomial.eval_zero] at this
    exact (pow_ne_zero k (by norm_num : (3 : ℤ) ≠ 0)) this.symm
  refine ⟨hγ, hmul, ⟨p, ?_, ?_, ?_⟩, ⟨rogersPoly2 k * rogersPoly3 k, ?_⟩⟩
  · rw [← hfq, toQSeries_apply, ← hp, Polynomial.map_map]
    congr 2
  · rw [← Polynomial.natDegree_map_eq_of_injective (f := Nat.castRingHom ℤ) Nat.cast_injective,
      hp, Polynomial.natDegree_mul h2ne h3ne, rogersPoly2_natDegree, rogersPoly3_natDegree]
  · have h1 : ((p.eval 1 : ℕ) : ℤ) = (rogersPoly2 k * rogersPoly3 k).eval 1 := by
      rw [← hp, Polynomial.eval_map, Polynomial.eval₂_at_one]
      rfl
    rw [Polynomial.eval_mul, rogersPoly2_eval_one, rogersPoly3_eval_one, ← mul_pow] at h1
    norm_num at h1
    exact_mod_cast h1
  · rw [hmul, ← hfq, toQSeries_apply]

end ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogers_factorisation
