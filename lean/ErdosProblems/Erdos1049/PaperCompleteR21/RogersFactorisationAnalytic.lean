import ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import ErdosProblems.Erdos1049.PositiveSeriesR16
import Mathlib

/-!
# Erdős #1049: the moment weights as a product of two finite sums, at real `q`

Completes `long1049:prop:rogers-factorisation` (core.tex, subsection "The size of `V_N^*` at a
fixed base"): the formal clauses are `rogers_factorisation` in `RogersFactorisation.lean`;
this file adds every clause stated for a fixed real `0 < q < 1`, and
`rogers_factorisation_proposition` states the whole proposition.

## Objects at real `q`

The paper fixes `0 < q < 1`, writes `P = (q;q)_∞`, `c_k = (k+1)^2 (k+2)/2`,
`G_q(w) = (w;q)_∞^{-3} ∑_{t ≥ 0} w^t/(q;q)_t · (q^t w^2;q)_∞/(q^t w;q)_∞^2` and
`γ_k = [w^k] G_q(w)`.  Here `G_q(w)` is the tree's `PaperR12.actualGeneratingFunction q w`, and
`(x;q)_n`, `(x;q)_∞` are the tree's `PaperR10.qPochhammerFinite x q n` and
`PaperR10.qPochhammerInfinity x q` (proved to be the limit of the finite products for
`0 ≤ x < 1`).  The coefficient sequence of `G_q` on `[0,1)` is unique
(`eq_of_hasSum_on_unit_interval`), so the theorem quantifies over every `γ` with
`∑_k γ_k w^k = G_q(w)` on `[0,1)`, and shows that one exists.

## How the formal identity is evaluated

* `hasSum_qBinomialRatio`: the real `q`-binomial theorem, from the tree's functional-equation
  lemmas `PaperR16.coeffEval_functional_equation` and `PaperR16.coeffEval_tendsto_geometric`;
  Euler's `∑ x^n/(q;q)_n = 1/(x;q)_∞` is its case `a = 0`.
* `absConv q`: the subring of `ℚ⟦X⟧` of series absolutely convergent at `q`, with the evaluation
  ring homomorphism `evq q`.  Every `1/(q;q)_n` lies in it.
* `formB_real`: the formal identity `rogersSeries_eq_formB` (a form of `G_q` with
  nonnegative coefficients, derived from `momentGenFun_eq_rogersSeries`) is lifted to power
  series with coefficients in `absConv q` and pushed through `evq q`, giving an identity of real
  power series in `w`.
* `hasSum_realGamma`: evaluating that identity at `0 ≤ w < 1` gives
  `∑_k R_k^{(2)}(q) R_k^{(3)}(q)/(q;q)_k · w^k = G_q(w)`.

## The weights

With `a_k = P^4 γ_k`: `weight_bounds` (`P^5 c_k ≤ a_k ≤ P^{-1} c_k`), `weight_ratio_le`
(`a_{k+h}/a_k ≤ P^{-6} (1+h)^3`), `weight_pos`, and `tendsto_weight_ratio`
(`a_{k+h}/a_k → 1` for each fixed `h`).  The last is proved from the increments of
`b_k^{(r)} = R_k^{(r)}/(q;q)_k`: `0 ≤ b^{(2)}_{k+1} - b^{(2)}_k ≤ 2P^{-2}` and
`0 ≤ b^{(3)}_{k+1} - b^{(3)}_k ≤ 3(k+1)P^{-3}`, against `b^{(2)}_k ≥ k+1` and
`b^{(3)}_k ≥ (k+1)(k+2)/2`.  The paper's proof of the proposition gives only the shift bound and
takes the fixed-shift limit from the later expansion in `long1049:thm:sharp-fixed-base`; this
file proves the limit directly.
-/

noncomputable section

namespace ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation

open PowerSeries Finset Filter
open scoped Topology PowerSeries.WithPiTopology
open ErdosProblems.Erdos1049 (qPochhammer gaussBinom)
open ErdosProblems.Erdos1049.PaperR10 (qPochhammerFinite qPochhammerInfinity qBinomialRatioCoeff)
open ErdosProblems.Erdos1049.PaperR16 (coeffEval coeffConv)
open ErdosProblems.Erdos1049.PaperR12 (actualGeneratingTerm actualGeneratingFunction)

/-! ### The real `q`-binomial theorem -/

section RealQBinomial

variable {q : ℝ}

lemma qPochhammerFinite_zero_left (q : ℝ) (n : ℕ) : qPochhammerFinite 0 q n = 1 := by
  simp [qPochhammerFinite]

lemma qPochhammerInfinity_zero_left (q : ℝ) : qPochhammerInfinity 0 q = 1 := by
  simp [qPochhammerInfinity]

/-- The real `q`-binomial theorem: for `0 < q < 1`, `0 ≤ a ≤ 1` and `0 ≤ x < 1`,
`∑_j (a;q)_j/(q;q)_j x^j = (ax;q)_∞/(x;q)_∞`. -/
theorem hasSum_qBinomialRatio (hq0 : 0 < q) (hq1 : q < 1) {a x : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun j => qBinomialRatioCoeff a q j * x ^ j)
      (qPochhammerInfinity (a * x) q / qPochhammerInfinity x q) := by
  set c := qBinomialRatioCoeff a q with hc
  have hc0 : ∀ n, 0 ≤ c n := PaperR10.qBinomialRatioCoeff_nonneg ha0 ha1 hq0.le hq1
  have hcC : ∀ n, c n ≤ (qPochhammerInfinity q q)⁻¹ :=
    PaperR10.qBinomialRatioCoeff_upper ha0 ha1 hq0.le hq1
  have hcz : c 0 = 1 := rfl
  have hsum : ∀ y, 0 ≤ y → y < 1 → Summable (fun n => c n * y ^ n) :=
    fun y hy0 hy1 => PaperR16.summable_coeffEval_of_bounded hc0 hcC hy0 hy1
  have hrec : ∀ n : ℕ, c (n + 1) * (1 - q ^ (n + 1)) = c n * (1 + (-a) * q ^ n) := by
    intro n
    have hlt : q ^ (n + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero n)
    have hne : (1 : ℝ) - q ^ (n + 1) ≠ 0 := by linarith
    simp only [hc, qBinomialRatioCoeff]
    field_simp
    ring
  have hfun : ∀ y, 0 ≤ y → y < 1 →
      (1 - y) * coeffEval c y = (1 - a * y) * coeffEval c (q * y) := by
    intro y hy0 hy1
    have hqy0 : 0 ≤ q * y := mul_nonneg hq0.le hy0
    have hqy1 : q * y < 1 := by nlinarith
    have h := PaperR16.coeffEval_functional_equation (hsum y hy0 hy1) (hsum (q * y) hqy0 hqy1) hrec
    linear_combination h
  have hiter : ∀ N : ℕ, coeffEval c x * qPochhammerFinite x q N =
      qPochhammerFinite (a * x) q N * coeffEval c (q ^ N * x) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        have hy0 : 0 ≤ q ^ N * x := mul_nonneg (pow_nonneg hq0.le N) hx0
        have hy1 : q ^ N * x < 1 :=
          lt_of_le_of_lt (mul_le_of_le_one_left hx0 (pow_le_one₀ hq0.le hq1.le)) hx1
        have hf := hfun (q ^ N * x) hy0 hy1
        rw [show q * (q ^ N * x) = q ^ (N + 1) * x by ring] at hf
        rw [PaperR10.qPochhammerFinite_succ, PaperR10.qPochhammerFinite_succ, ← mul_assoc, ih]
        linear_combination (qPochhammerFinite (a * x) q N) * hf
  have hax0 : 0 ≤ a * x := mul_nonneg ha0 hx0
  have hax1 : a * x < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hx0 ha1) hx1
  have hP1 := PaperR10.tendsto_qPochhammerFinite hx0 hx1 hq0.le hq1
  have hP2 := PaperR10.tendsto_qPochhammerFinite hax0 hax1 hq0.le hq1
  have hF : Tendsto (fun N : ℕ => coeffEval c (q ^ N * x)) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat 1).mp
      (PaperR16.coeffEval_tendsto_geometric hc0 hcC hcz hq0.le hq1 hx0 hx1.le)
  have hL : Tendsto (fun N => qPochhammerFinite (a * x) q N * coeffEval c (q ^ N * x)) atTop
      (𝓝 (coeffEval c x * qPochhammerInfinity x q)) :=
    (hP1.const_mul (coeffEval c x)).congr hiter
  have hR : Tendsto (fun N => qPochhammerFinite (a * x) q N * coeffEval c (q ^ N * x)) atTop
      (𝓝 (qPochhammerInfinity (a * x) q * 1)) := hP2.mul hF
  have heq := tendsto_nhds_unique hL hR
  have hpos := PaperR10.qPochhammerInfinity_pos x q
  have hval : coeffEval c x = qPochhammerInfinity (a * x) q / qPochhammerInfinity x q := by
    rw [eq_div_iff hpos.ne', heq, mul_one]
  have hs := (hsum x hx0 hx1).hasSum
  rw [show (∑' n, c n * x ^ n) = coeffEval c x from rfl, hval] at hs
  exact hs

/-- Euler's formula `∑_n x^n/(q;q)_n = 1/(x;q)_∞` for `0 ≤ x < 1`. -/
theorem hasSum_euler_inv (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n => (qPochhammerFinite q q n)⁻¹ * x ^ n) (qPochhammerInfinity x q)⁻¹ := by
  have h := hasSum_qBinomialRatio hq0 hq1 le_rfl zero_le_one hx0 hx1
  rw [zero_mul, qPochhammerInfinity_zero_left, one_div] at h
  convert h using 1
  funext n
  rw [PaperR10.qBinomialRatioCoeff_eq_ratio hq0.le hq1, qPochhammerFinite_zero_left, one_div]

lemma qPochhammerFinite_q_pos (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 < qPochhammerFinite q q n :=
  PaperR10.qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le n

lemma qPochhammerFinite_q_le_one (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    qPochhammerFinite q q n ≤ 1 :=
  (PaperR10.qPochhammerFinite_nonneg_le_one hq0.le hq1.le hq0.le hq1.le n).2

lemma P_le_qPochhammerFinite (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    qPochhammerInfinity q q ≤ qPochhammerFinite q q n :=
  PaperR10.qPochhammerInfinity_le_finite hq0.le hq1 hq0.le hq1 n

end RealQBinomial

/-! ### Power series over `ℚ` absolutely convergent at a real point -/

section AbsConv

variable (q : ℝ)

/-- The real terms `c_n q^n` of a power series `∑ c_n X^n` over `ℚ`. -/
def realTerms (f : PowerSeries ℚ) (n : ℕ) : ℝ := ((coeff n f : ℚ) : ℝ) * q ^ n

lemma realTerms_mul (f g : PowerSeries ℚ) (n : ℕ) :
    realTerms q (f * g) n = ∑ p ∈ antidiagonal n, realTerms q f p.1 * realTerms q g p.2 := by
  simp only [realTerms, coeff_mul, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring

/-- The subring of `ℚ⟦X⟧` of power series that converge absolutely at `q`. -/
def absConv : Subring (PowerSeries ℚ) where
  carrier := {f | Summable (fun n => ‖realTerms q f n‖)}
  mul_mem' {f g} hf hg := by
    have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
    simp only [Set.mem_setOf_eq]
    exact h.congr fun n => by rw [realTerms_mul]
  one_mem' := by
    show Summable _
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    simp [realTerms, coeff_one, hn]
  add_mem' {f g} hf hg := by
    show Summable _
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hf.add hg)
    simp only [realTerms, map_add, Rat.cast_add, add_mul]
    exact norm_add_le _ _
  zero_mem' := by
    show Summable _
    simp [realTerms]
  neg_mem' {f} hf := by
    show Summable _
    simpa [realTerms] using hf

lemma summable_realTerms {f : PowerSeries ℚ} (hf : f ∈ absConv q) :
    Summable (realTerms q f) := Summable.of_norm hf

/-- Evaluation at `q` of an absolutely convergent power series. -/
def evq : absConv q →+* ℝ where
  toFun f := ∑' n, realTerms q f.1 n
  map_one' := by
    change ∑' n, realTerms q 1 n = 1
    rw [tsum_eq_single 0]
    · simp [realTerms]
    · intro n hn
      simp [realTerms, coeff_one, hn]
  map_mul' f g := by
    change ∑' n, realTerms q (f.1 * g.1) n =
      (∑' n, realTerms q f.1 n) * ∑' n, realTerms q g.1 n
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm f.2 g.2]
    exact tsum_congr fun n => realTerms_mul q f.1 g.1 n
  map_zero' := by
    change ∑' n, realTerms q 0 n = 0
    simp [realTerms]
  map_add' f g := by
    change ∑' n, realTerms q (f.1 + g.1) n =
      (∑' n, realTerms q f.1 n) + ∑' n, realTerms q g.1 n
    rw [← (summable_realTerms q f.2).tsum_add (summable_realTerms q g.2)]
    exact tsum_congr fun n => by simp [realTerms, add_mul]

lemma hasSum_evq (f : absConv q) : HasSum (realTerms q f.1) (evq q f) :=
  (summable_realTerms q f.2).hasSum

lemma X_mem_absConv : (PowerSeries.X : PowerSeries ℚ) ∈ absConv q := by
  show Summable _
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  simp only [Finset.mem_singleton] at hn
  simp [realTerms, coeff_X, hn]

/-- `q` as an element of the subring. -/
def qA : absConv q := ⟨PowerSeries.X, X_mem_absConv q⟩

lemma evq_qA : evq q (qA q) = q := by
  change ∑' n, realTerms q PowerSeries.X n = q
  rw [tsum_eq_single 1]
  · simp [realTerms]
  · intro n hn
    simp [realTerms, coeff_X, hn]

variable {q}

lemma one_sub_X_pow_inv_eq {m : ℕ} (hm : m ≠ 0) :
    (1 - PowerSeries.X ^ m : PowerSeries ℚ)⁻¹ = expand m hm (mk 1) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp [zero_pow hm])]
  have h := congrArg (expand m hm) (PowerSeries.mk_one_mul_one_sub_eq_one (S := ℚ))
  rwa [map_mul, map_sub, map_one, expand_X] at h

lemma geom_mem_absConv (hq0 : 0 ≤ q) (hq1 : q < 1) {m : ℕ} (hm : m ≠ 0) :
    (1 - PowerSeries.X ^ m : PowerSeries ℚ)⁻¹ ∈ absConv q := by
  rw [one_sub_X_pow_inv_eq hm]
  show Summable _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one hq0 hq1)
  simp only [realTerms, coeff_expand]
  split_ifs
  · simp [abs_of_nonneg hq0]
  · simp [pow_nonneg hq0 n]

lemma ifac_succ_eq (n : ℕ) : ifac (n + 1) = ifac n * (1 - qq ^ (n + 1))⁻¹ := by
  rw [ifac, ifac, qfac_succ, PowerSeries.mul_inv_rev, mul_comm]

lemma ifac_mem_absConv (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) : ifac n ∈ absConv q := by
  induction n with
  | zero => rw [ifac_zero]; exact (absConv q).one_mem
  | succ n ih =>
      rw [ifac_succ_eq]
      exact (absConv q).mul_mem ih (geom_mem_absConv hq0 hq1 (Nat.succ_ne_zero n))

/-- `1/(q;q)_n` as an element of the subring. -/
def ifacA (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) : absConv q :=
  ⟨ifac n, ifac_mem_absConv hq0 hq1 n⟩

lemma map_qPochhammer {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a z : R) (n : ℕ) :
    f (qPochhammer a z n) = qPochhammer (f a) (f z) n := by
  induction n with
  | zero => simp [ErdosProblems.Erdos1049.qPochhammer]
  | succ n ih =>
      rw [ErdosProblems.Erdos1049.qPochhammer_succ, ErdosProblems.Erdos1049.qPochhammer_succ,
        map_mul, ih, map_sub, map_one, map_mul, map_pow]

lemma qPochhammer_eq_qPochhammerFinite (a z : ℝ) (n : ℕ) :
    qPochhammer a z n = qPochhammerFinite z a n := by
  induction n with
  | zero => simp [ErdosProblems.Erdos1049.qPochhammer]
  | succ n ih =>
      rw [ErdosProblems.Erdos1049.qPochhammer_succ, PaperR10.qPochhammerFinite_succ, ih]

variable (q) in
/-- `(q;q)_n` as an element of the subring. -/
def qfacA (n : ℕ) : absConv q := qPochhammer (qA q) (qA q) n

lemma qfacA_val (n : ℕ) : ((qfacA q n : absConv q) : PowerSeries ℚ) = qfac n := by
  have h := map_qPochhammer (absConv q).subtype (qA q) (qA q) n
  exact h

lemma evq_qfacA (n : ℕ) : evq q (qfacA q n) = qPochhammerFinite q q n := by
  rw [qfacA, map_qPochhammer, evq_qA, qPochhammer_eq_qPochhammerFinite]

lemma ifacA_mul_qfacA (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ifacA hq0 hq1 n * qfacA q n = 1 := by
  apply Subtype.ext
  change ifac n * ((qfacA q n : absConv q) : PowerSeries ℚ) = 1
  rw [qfacA_val, ifac_mul_qfac]

lemma evq_ifacA (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    evq q (ifacA hq0 hq1 n) = (qPochhammerFinite q q n)⁻¹ := by
  have h := congrArg (evq q) (ifacA_mul_qfacA hq0 hq1 n)
  rw [map_mul, map_one, evq_qfacA] at h
  exact eq_inv_of_mul_eq_one_left h

end AbsConv

/-! ### The Rogers sums at a real point, lifted and evaluated -/

/-- `R_k^{(r)}(q) = ∑_{n_1+⋯+n_r=k} (q;q)_k / ∏_{j ≤ r} (q;q)_{n_j}` at a real number `q`. -/
def realRogersR (r k : ℕ) (q : ℝ) : ℝ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, qPochhammerFinite q q k / ∏ j, qPochhammerFinite q q (n j)

/-- `R_k^{(2)}(q) R_k^{(3)}(q) / (q;q)_k` at a real number `q`. -/
def realGamma (q : ℝ) (k : ℕ) : ℝ :=
  realRogersR 2 k q * realRogersR 3 k q / qPochhammerFinite q q k

lemma inv_qfac_mul3 (a b c : ℕ) : (qfac a * qfac b * qfac c)⁻¹ = ifac a * ifac b * ifac c := by
  simp only [ifac]
  rw [PowerSeries.mul_inv_rev, PowerSeries.mul_inv_rev]
  ring

section Lift

variable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)

/-- `R_k^{(2)}` in the subring. -/
def R2A (k : ℕ) : absConv q :=
  ∑ x ∈ Finset.Nat.antidiagonalTuple 2 k, qfacA q k * (ifacA hq0 hq1 (x 0) * ifacA hq0 hq1 (x 1))

/-- `R_k^{(3)}` in the subring. -/
def R3A (k : ℕ) : absConv q :=
  ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
    qfacA q k * (ifacA hq0 hq1 (x 0) * ifacA hq0 hq1 (x 1) * ifacA hq0 hq1 (x 2))

/-- `R_k^{(2)} R_k^{(3)} / (q;q)_k` in the subring. -/
def rogersA (k : ℕ) : absConv q := R2A hq0 hq1 k * R3A hq0 hq1 k * ifacA hq0 hq1 k

lemma R2A_val (k : ℕ) : (absConv q).subtype (R2A hq0 hq1 k) = rogersR 2 k := by
  rw [R2A, map_sum, rogersR]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_mul, Fin.prod_univ_two, inv_qfac_mul]
  change ((qfacA q k : absConv q) : PowerSeries ℚ) * (ifac (x 0) * ifac (x 1)) = _
  rw [qfacA_val]

lemma R3A_val (k : ℕ) : (absConv q).subtype (R3A hq0 hq1 k) = rogersR 3 k := by
  rw [R3A, map_sum, rogersR]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_mul, map_mul, Fin.prod_univ_three, inv_qfac_mul3]
  change ((qfacA q k : absConv q) : PowerSeries ℚ) * (ifac (x 0) * ifac (x 1) * ifac (x 2)) = _
  rw [qfacA_val]

lemma rogersA_val (k : ℕ) :
    (absConv q).subtype (rogersA hq0 hq1 k) = rogersR 2 k * rogersR 3 k * ifac k := by
  rw [rogersA, map_mul, map_mul, R2A_val, R3A_val]
  rfl

lemma evq_R2A (k : ℕ) : evq q (R2A hq0 hq1 k) = realRogersR 2 k q := by
  rw [R2A, map_sum, realRogersR]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_mul, evq_qfacA, evq_ifacA, evq_ifacA, Fin.prod_univ_two, div_eq_mul_inv,
    mul_inv]

lemma evq_R3A (k : ℕ) : evq q (R3A hq0 hq1 k) = realRogersR 3 k q := by
  rw [R3A, map_sum, realRogersR]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_mul, map_mul, evq_qfacA, evq_ifacA, evq_ifacA, evq_ifacA,
    Fin.prod_univ_three, div_eq_mul_inv, mul_inv, mul_inv]

lemma evq_rogersA (k : ℕ) : evq q (rogersA hq0 hq1 k) = realGamma q k := by
  rw [rogersA, map_mul, map_mul, evq_R2A, evq_R3A, evq_ifacA, realGamma, div_eq_mul_inv]

end Lift

/-! ### Transfer of the formal identity to real coefficients -/

/-- `∑_i w^i F_i` over an arbitrary coefficient ring. -/
def wsumG {R : Type*} [Semiring R] (F : ℕ → PowerSeries R) : PowerSeries R :=
  mk fun n => ∑ i ∈ range (n + 1), coeff (n - i) (F i)

lemma coeff_wsumG {R : Type*} [Semiring R] (F : ℕ → PowerSeries R) (n : ℕ) :
    coeff n (wsumG F) = ∑ i ∈ range (n + 1), coeff (n - i) (F i) := coeff_mk _ _

lemma map_wsumG {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (F : ℕ → PowerSeries R) :
    PowerSeries.map φ (wsumG F) = wsumG (fun i => PowerSeries.map φ (F i)) := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_map, coeff_wsumG, map_sum]

lemma wsumG_eq_wsum (F : ℕ → BW) : wsumG F = wsum F := rfl

/-- The formal identity in the form with nonnegative coefficients:
`∑_k R_k^{(2)}R_k^{(3)}/(q;q)_k w^k =
E(w)^2 ∑_t w^t/(q;q)_t (∑_j q^{tj} w^j/(q;q)_j E(q^j w)) E(q^t w)`. -/
theorem rogersSeries_eq_formB :
    rogersSeries = eE ^ 2 * wsum (fun t => C (ifac t) *
      (wsum (fun j => C (qq ^ (t * j) * ifac j) * rescale (qq ^ j) eE) * rescale (qq ^ t) eE)) := by
  rw [← momentGenFun_eq_rogersSeries]
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
  refine congrArg (fun X => eE ^ 2 * X) (wsum_congr fun t => ?_)
  rw [show eE * (C (ifac t) * ((expand 2 two_ne_zero (rescale (qq ^ t) eP) *
      rescale (qq ^ t) eE) * rescale (qq ^ t) eE)) =
      C (ifac t) * ((eE * (expand 2 two_ne_zero (rescale (qq ^ t) eP) *
      rescale (qq ^ t) eE)) * rescale (qq ^ t) eE) by ring, eE_mul_qbinomial_w]

section Transfer

variable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)

/-- `E(w) = ∑_n w^n/(q;q)_n` with coefficients in the subring. -/
def eEA : PowerSeries (absConv q) := mk fun n => ifacA hq0 hq1 n

/-- The nonnegative form of `G_q` with coefficients in the subring. -/
def formBA : PowerSeries (absConv q) :=
  eEA hq0 hq1 ^ 2 * wsumG (fun t => C (ifacA hq0 hq1 t) *
    (wsumG (fun j => C (qA q ^ (t * j) * ifacA hq0 hq1 j) * rescale (qA q ^ j) (eEA hq0 hq1)) *
      rescale (qA q ^ t) (eEA hq0 hq1)))

/-- `∑_k R_k^{(2)}R_k^{(3)}/(q;q)_k w^k` with coefficients in the subring. -/
def rogersSeriesA : PowerSeries (absConv q) := mk fun n => rogersA hq0 hq1 n

lemma map_subtype_eEA : PowerSeries.map (absConv q).subtype (eEA hq0 hq1) = eE := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_map, eEA, coeff_mk, coeff_eE]
  rfl

lemma map_subtype_formBA : PowerSeries.map (absConv q).subtype (formBA hq0 hq1) =
    eE ^ 2 * wsum (fun t => C (ifac t) *
      (wsum (fun j => C (qq ^ (t * j) * ifac j) * rescale (qq ^ j) eE) * rescale (qq ^ t) eE)) := by
  have hqA : (absConv q).subtype (qA q) = qq := rfl
  have hif : ∀ n, (absConv q).subtype (ifacA hq0 hq1 n) = ifac n := fun n => rfl
  simp only [formBA, map_mul, map_pow, map_wsumG, map_C, ← rescale_map, map_subtype_eEA, hqA,
    hif, ← wsumG_eq_wsum]

lemma map_subtype_rogersSeriesA :
    PowerSeries.map (absConv q).subtype (rogersSeriesA hq0 hq1) = rogersSeries := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_map, rogersSeriesA, coeff_mk, rogersA_val, rogersSeries, coeff_mk]

theorem formBA_eq : formBA hq0 hq1 = rogersSeriesA hq0 hq1 := by
  apply PowerSeries.map_injective (absConv q).subtype Subtype.val_injective
  rw [map_subtype_formBA, map_subtype_rogersSeriesA, rogersSeries_eq_formB]

/-- `E(w) = ∑_n w^n/(q;q)_n` over the reals. -/
def eER (q : ℝ) : PowerSeries ℝ := mk fun n => (qPochhammerFinite q q n)⁻¹

lemma map_evq_eEA : PowerSeries.map (evq q) (eEA hq0 hq1) = eER q := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_map, eEA, coeff_mk, evq_ifacA, eER, coeff_mk]

include hq0 hq1 in
/-- The formal identity with real coefficients at the real point `q`. -/
theorem formB_real :
    eER q ^ 2 * wsumG (fun t => C (qPochhammerFinite q q t)⁻¹ *
      (wsumG (fun j => C (q ^ (t * j) * (qPochhammerFinite q q j)⁻¹) * rescale (q ^ j) (eER q)) *
        rescale (q ^ t) (eER q))) = mk (realGamma q) := by
  have hL : PowerSeries.map (evq q) (formBA hq0 hq1) =
      eER q ^ 2 * wsumG (fun t => C (qPochhammerFinite q q t)⁻¹ *
        (wsumG (fun j => C (q ^ (t * j) * (qPochhammerFinite q q j)⁻¹) *
          rescale (q ^ j) (eER q)) * rescale (q ^ t) (eER q))) := by
    simp only [formBA, map_mul, map_pow, map_wsumG, map_C, ← rescale_map, map_evq_eEA, evq_qA,
      evq_ifacA]
  have hR : PowerSeries.map (evq q) (rogersSeriesA hq0 hq1) = mk (realGamma q) := by
    refine PowerSeries.ext fun n => ?_
    rw [coeff_map, rogersSeriesA, coeff_mk, coeff_mk, evq_rogersA]
  rw [← hL, ← hR, formBA_eq]

end Transfer

/-! ### Real evaluation of power series with nonnegative coefficients -/

section RealEval

lemma hasSum_sum_antidiagonal {f : ℕ × ℕ → ℝ} {a : ℝ} (hf : HasSum f a) :
    HasSum (fun n => ∑ p ∈ antidiagonal n, f p) a := by
  have h := (Finset.sigmaAntidiagonalEquivProd.hasSum_iff (f := f)).mpr hf
  have h2 := h.sigma (fun n => hasSum_fintype _)
  convert h2 using 1
  funext n
  rw [← Finset.sum_coe_sort]
  rfl

lemma coeff_mul_nonneg {f g : PowerSeries ℝ} (hf0 : ∀ n, 0 ≤ coeff n f)
    (hg0 : ∀ n, 0 ≤ coeff n g) (n : ℕ) : 0 ≤ coeff n (f * g) := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hf0 _) (hg0 _)

lemma hasSum_coeff_mul {f g : PowerSeries ℝ} {w u v : ℝ} (hw : 0 ≤ w)
    (hf0 : ∀ n, 0 ≤ coeff n f) (hg0 : ∀ n, 0 ≤ coeff n g)
    (hf : HasSum (fun n => coeff n f * w ^ n) u) (hg : HasSum (fun n => coeff n g * w ^ n) v) :
    HasSum (fun n => coeff n (f * g) * w ^ n) (u * v) := by
  have h := PaperR16.coeffConv_hasSum (a := fun n => coeff n f) (b := fun n => coeff n g)
    hf0 hg0 hw hf.summable hg.summable
  rw [show coeffEval (fun n => coeff n f) w = u from hf.tsum_eq,
    show coeffEval (fun n => coeff n g) w = v from hg.tsum_eq] at h
  convert h using 1
  funext n
  rw [coeff_mul]
  rfl

lemma hasSum_coeff_rescale {f : PowerSeries ℝ} {a w v : ℝ}
    (h : HasSum (fun n => coeff n f * (a * w) ^ n) v) :
    HasSum (fun n => coeff n (rescale a f) * w ^ n) v := by
  convert h using 1
  funext n
  rw [coeff_rescale, mul_pow]
  ring

lemma hasSum_coeff_C_mul {f : PowerSeries ℝ} {c w v : ℝ}
    (h : HasSum (fun n => coeff n f * w ^ n) v) :
    HasSum (fun n => coeff n (C c * f) * w ^ n) (c * v) := by
  convert h.mul_left c using 1
  funext n
  rw [coeff_C_mul]
  ring

lemma coeff_wsumG_nonneg {F : ℕ → PowerSeries ℝ} (hF0 : ∀ t n, 0 ≤ coeff n (F t)) (n : ℕ) :
    0 ≤ coeff n (wsumG F) := by
  rw [coeff_wsumG]
  exact Finset.sum_nonneg fun t _ => hF0 _ _

lemma hasSum_coeff_wsumG {F : ℕ → PowerSeries ℝ} {w : ℝ} {v : ℕ → ℝ} (hw : 0 ≤ w)
    (hF0 : ∀ t n, 0 ≤ coeff n (F t)) (hF : ∀ t, HasSum (fun n => coeff n (F t) * w ^ n) (v t))
    (hv : Summable (fun t => w ^ t * v t)) :
    HasSum (fun n => coeff n (wsumG F) * w ^ n) (∑' t, w ^ t * v t) := by
  set g : ℕ × ℕ → ℝ := fun p => w ^ p.1 * (coeff p.2 (F p.1) * w ^ p.2) with hg
  have hg0 : 0 ≤ g := fun p =>
    mul_nonneg (pow_nonneg hw _) (mul_nonneg (hF0 _ _) (pow_nonneg hw _))
  have hrow : ∀ t, HasSum (fun m => g (t, m)) (w ^ t * v t) := fun t => (hF t).mul_left (w ^ t)
  have hsum : Summable g := (summable_prod_of_nonneg hg0).mpr
    ⟨fun t => (hrow t).summable, by simpa only [(hrow _).tsum_eq] using hv⟩
  have htot : HasSum g (∑' t, w ^ t * v t) := by
    rw [(hsum.hasSum.prod_fiberwise hrow).tsum_eq]
    exact hsum.hasSum
  have h := hasSum_sum_antidiagonal htot
  convert h using 1
  funext n
  rw [coeff_wsumG, Finset.sum_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htn : t ≤ n := Nat.lt_succ_iff.mp (mem_range.mp ht)
  simp only [hg]
  rw [show w ^ n = w ^ t * w ^ (n - t) by rw [← pow_add, Nat.add_sub_cancel' htn]]
  ring

end RealEval

/-! ### The real-`q` identity `∑_k γ_k w^k = G_q(w)` -/

section RealIdentity

variable {q : ℝ}

lemma coeff_eER (n : ℕ) : coeff n (eER q) = (qPochhammerFinite q q n)⁻¹ := coeff_mk _ _

lemma coeff_eER_nonneg (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 0 ≤ coeff n (eER q) := by
  rw [coeff_eER]
  exact inv_nonneg.mpr (qPochhammerFinite_q_pos hq0 hq1 n).le

lemma coeff_rescale_eER_nonneg (hq0 : 0 < q) (hq1 : q < 1) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ coeff n (rescale s (eER q)) := by
  rw [coeff_rescale]
  exact mul_nonneg (pow_nonneg hs n) (coeff_eER_nonneg hq0 hq1 n)

lemma hasSum_eER (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    HasSum (fun n => coeff n (eER q) * w ^ n) (qPochhammerInfinity w q)⁻¹ := by
  convert hasSum_euler_inv hq0 hq1 hw0 hw1 using 1
  funext n
  rw [coeff_eER]

lemma hasSum_rescale_eER (hq0 : 0 < q) (hq1 : q < 1) {s w : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    HasSum (fun n => coeff n (rescale s (eER q)) * w ^ n) (qPochhammerInfinity (s * w) q)⁻¹ := by
  apply hasSum_coeff_rescale
  have hsw0 : 0 ≤ s * w := mul_nonneg hs0 hw0
  have hsw1 : s * w < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hw0 hs1) hw1
  exact hasSum_eER hq0 hq1 hsw0 hsw1

/-- `1/(q^j w;q)_∞ = (w;q)_j / (w;q)_∞`. -/
lemma inv_qPochhammerInfinity_shift (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) (j : ℕ) :
    (qPochhammerInfinity (q ^ j * w) q)⁻¹ =
      qPochhammerFinite w q j * (qPochhammerInfinity w q)⁻¹ := by
  have h := PaperR12.qPochhammerInfinity_split hw0 hw1 hq0.le hq1 j
  have hpos := PaperR10.qPochhammerFinite_pos hw0 hw1 hq0.le hq1.le j
  have hpos2 := PaperR10.qPochhammerInfinity_pos (w * q ^ j) q
  rw [mul_comm (q ^ j) w, h]
  field_simp

lemma hasSum_inner (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (t : ℕ) :
    HasSum (fun j => w ^ j * (q ^ (t * j) * (qPochhammerFinite q q j)⁻¹ *
        (qPochhammerInfinity (q ^ j * w) q)⁻¹))
      ((qPochhammerInfinity w q)⁻¹ *
        (qPochhammerInfinity (q ^ t * w ^ 2) q / qPochhammerInfinity (q ^ t * w) q)) := by
  have hx0 : 0 ≤ q ^ t * w := mul_nonneg (pow_nonneg hq0.le t) hw0
  have hx1 : q ^ t * w < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left hw0 (pow_le_one₀ hq0.le hq1.le)) hw1
  have h := (hasSum_qBinomialRatio hq0 hq1 hw0 hw1.le hx0 hx1).mul_left
    (qPochhammerInfinity w q)⁻¹
  rw [show w * (q ^ t * w) = q ^ t * w ^ 2 by ring] at h
  convert h using 1
  funext j
  rw [inv_qPochhammerInfinity_shift hq0 hq1 hw0 hw1 j,
    PaperR10.qBinomialRatioCoeff_eq_ratio hq0.le hq1, mul_pow, ← pow_mul]
  ring

lemma actualGeneratingTerm_bounds (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) (t : ℕ) :
    0 ≤ actualGeneratingTerm q w t ∧ actualGeneratingTerm q w t ≤
      w ^ t * ((qPochhammerInfinity q q)⁻¹ * ((qPochhammerInfinity w q)⁻¹) ^ 2) := by
  have hP := PaperR10.qPochhammerInfinity_pos q q
  have hqt := qPochhammerFinite_q_pos hq0 hq1 t
  have hPle := P_le_qPochhammerFinite hq0 hq1 t
  have hy0 : 0 ≤ q ^ t * w ^ 2 := mul_nonneg (pow_nonneg hq0.le t) (pow_nonneg hw0 2)
  have hy1 : q ^ t * w ^ 2 < 1 := by
    have h1 : q ^ t ≤ 1 := pow_le_one₀ hq0.le hq1.le
    have h2 : w ^ 2 < 1 := by nlinarith
    nlinarith [pow_nonneg hq0.le t, pow_nonneg hw0 2]
  have hnum : qPochhammerInfinity (q ^ t * w ^ 2) q ≤ 1 := by
    have := PaperR10.qPochhammerInfinity_le_finite hy0 hy1 hq0.le hq1 0
    simpa using this
  have hnum0 := PaperR10.qPochhammerInfinity_pos (q ^ t * w ^ 2) q
  have hden0 := PaperR10.qPochhammerInfinity_pos (q ^ t * w) q
  have hw := PaperR10.qPochhammerInfinity_pos w q
  have hden : qPochhammerInfinity w q ≤ qPochhammerInfinity (q ^ t * w) q := by
    have h := PaperR12.qPochhammerInfinity_split hw0 hw1 hq0.le hq1 t
    have hle := PaperR10.qPochhammerFinite_nonneg_le_one hw0 hw1.le hq0.le hq1.le t
    rw [h, mul_comm (q ^ t) w]
    calc qPochhammerFinite w q t * qPochhammerInfinity (w * q ^ t) q
        ≤ 1 * qPochhammerInfinity (w * q ^ t) q :=
          mul_le_mul_of_nonneg_right hle.2 (PaperR10.qPochhammerInfinity_pos _ _).le
      _ = qPochhammerInfinity (w * q ^ t) q := one_mul _
  have hinv1 : (qPochhammerFinite q q t)⁻¹ ≤ (qPochhammerInfinity q q)⁻¹ := inv_anti₀ hP hPle
  have hinv2 : (qPochhammerInfinity (q ^ t * w) q ^ 2)⁻¹ ≤ (qPochhammerInfinity w q ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hw.le hden 2)
  unfold actualGeneratingTerm
  constructor
  · positivity
  · calc w ^ t / qPochhammerFinite q q t * qPochhammerInfinity (q ^ t * w ^ 2) q /
          qPochhammerInfinity (q ^ t * w) q ^ 2
        = w ^ t * ((qPochhammerFinite q q t)⁻¹ * (qPochhammerInfinity (q ^ t * w ^ 2) q *
            (qPochhammerInfinity (q ^ t * w) q ^ 2)⁻¹)) := by ring
      _ ≤ w ^ t * ((qPochhammerInfinity q q)⁻¹ * (1 * (qPochhammerInfinity w q ^ 2)⁻¹)) := by
          gcongr
      _ = w ^ t * ((qPochhammerInfinity q q)⁻¹ * ((qPochhammerInfinity w q)⁻¹) ^ 2) := by
          rw [one_mul, inv_pow]

lemma summable_actualGeneratingTerm (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) : Summable (actualGeneratingTerm q w) :=
  Summable.of_nonneg_of_le (fun t => (actualGeneratingTerm_bounds hq0 hq1 hw0 hw1 t).1)
    (fun t => (actualGeneratingTerm_bounds hq0 hq1 hw0 hw1 t).2)
    ((summable_geometric_of_lt_one hw0 hw1).mul_right _)

/-- The inner series `∑_j q^{tj} w^j/(q;q)_j · E(q^j w)`. -/
def innerSeries (q : ℝ) (t : ℕ) : PowerSeries ℝ :=
  wsumG (fun j => C (q ^ (t * j) * (qPochhammerFinite q q j)⁻¹) * rescale (q ^ j) (eER q))

/-- The `t`-th outer summand `(q;q)_t^{-1} (∑_j ...) E(q^t w)`. -/
def outerTerm (q : ℝ) (t : ℕ) : PowerSeries ℝ :=
  C (qPochhammerFinite q q t)⁻¹ * (innerSeries q t * rescale (q ^ t) (eER q))

lemma coeff_innerSeries_nonneg (hq0 : 0 < q) (hq1 : q < 1) (t n : ℕ) :
    0 ≤ coeff n (innerSeries q t) := by
  refine coeff_wsumG_nonneg (fun j m => ?_) n
  rw [coeff_C_mul]
  exact mul_nonneg (mul_nonneg (pow_nonneg hq0.le _)
    (inv_nonneg.mpr (qPochhammerFinite_q_pos hq0 hq1 j).le))
    (coeff_rescale_eER_nonneg hq0 hq1 (pow_nonneg hq0.le j) m)

lemma coeff_outerTerm_nonneg (hq0 : 0 < q) (hq1 : q < 1) (t n : ℕ) :
    0 ≤ coeff n (outerTerm q t) := by
  rw [outerTerm, coeff_C_mul]
  exact mul_nonneg (inv_nonneg.mpr (qPochhammerFinite_q_pos hq0 hq1 t).le)
    (coeff_mul_nonneg (coeff_innerSeries_nonneg hq0 hq1 t)
      (coeff_rescale_eER_nonneg hq0 hq1 (pow_nonneg hq0.le t)) n)

lemma hasSum_innerSeries (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1)
    (t : ℕ) :
    HasSum (fun n => coeff n (innerSeries q t) * w ^ n)
      ((qPochhammerInfinity w q)⁻¹ *
        (qPochhammerInfinity (q ^ t * w ^ 2) q / qPochhammerInfinity (q ^ t * w) q)) := by
  have hinner := hasSum_inner hq0 hq1 hw0 hw1 t
  have h := hasSum_coeff_wsumG hw0
    (F := fun j => C (q ^ (t * j) * (qPochhammerFinite q q j)⁻¹) * rescale (q ^ j) (eER q))
    (v := fun j => q ^ (t * j) * (qPochhammerFinite q q j)⁻¹ *
      (qPochhammerInfinity (q ^ j * w) q)⁻¹)
    (fun j m => by
      rw [coeff_C_mul]
      exact mul_nonneg (mul_nonneg (pow_nonneg hq0.le _)
        (inv_nonneg.mpr (qPochhammerFinite_q_pos hq0 hq1 j).le))
        (coeff_rescale_eER_nonneg hq0 hq1 (pow_nonneg hq0.le j) m))
    (fun j => hasSum_coeff_C_mul (hasSum_rescale_eER hq0 hq1 (pow_nonneg hq0.le j)
      (pow_le_one₀ hq0.le hq1.le) hw0 hw1))
    hinner.summable
  rw [hinner.tsum_eq] at h
  exact h

lemma hasSum_outerTerm (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1)
    (t : ℕ) :
    HasSum (fun n => coeff n (outerTerm q t) * w ^ n)
      ((qPochhammerFinite q q t)⁻¹ * (((qPochhammerInfinity w q)⁻¹ *
        (qPochhammerInfinity (q ^ t * w ^ 2) q / qPochhammerInfinity (q ^ t * w) q)) *
          (qPochhammerInfinity (q ^ t * w) q)⁻¹)) :=
  hasSum_coeff_C_mul (hasSum_coeff_mul hw0 (coeff_innerSeries_nonneg hq0 hq1 t)
    (coeff_rescale_eER_nonneg hq0 hq1 (pow_nonneg hq0.le t))
    (hasSum_innerSeries hq0 hq1 hw0 hw1 t)
    (hasSum_rescale_eER hq0 hq1 (pow_nonneg hq0.le t) (pow_le_one₀ hq0.le hq1.le) hw0 hw1))

lemma outer_value_eq (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (t : ℕ) :
    w ^ t * ((qPochhammerFinite q q t)⁻¹ * (((qPochhammerInfinity w q)⁻¹ *
        (qPochhammerInfinity (q ^ t * w ^ 2) q / qPochhammerInfinity (q ^ t * w) q)) *
          (qPochhammerInfinity (q ^ t * w) q)⁻¹)) =
      (qPochhammerInfinity w q)⁻¹ * actualGeneratingTerm q w t := by
  have h1 := (qPochhammerFinite_q_pos hq0 hq1 t).ne'
  have h2 := (PaperR10.qPochhammerInfinity_pos (q ^ t * w) q).ne'
  have h3 := (PaperR10.qPochhammerInfinity_pos w q).ne'
  unfold actualGeneratingTerm
  field_simp

lemma formB_real' (hq0 : 0 < q) (hq1 : q < 1) :
    eER q ^ 2 * wsumG (outerTerm q) = mk (realGamma q) :=
  formB_real hq0.le hq1

/-- The real-`q` identity: for `0 < q < 1` and `0 ≤ w < 1`,
`∑_k R_k^{(2)}(q) R_k^{(3)}(q)/(q;q)_k · w^k = G_q(w)`. -/
theorem hasSum_realGamma (hq0 : 0 < q) (hq1 : q < 1) {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    HasSum (fun k => realGamma q k * w ^ k) (actualGeneratingFunction q w) := by
  have hsummable : Summable (fun t => w ^ t * ((qPochhammerFinite q q t)⁻¹ *
      (((qPochhammerInfinity w q)⁻¹ *
        (qPochhammerInfinity (q ^ t * w ^ 2) q / qPochhammerInfinity (q ^ t * w) q)) *
          (qPochhammerInfinity (q ^ t * w) q)⁻¹))) := by
    simp_rw [outer_value_eq hq0 hq1]
    exact (summable_actualGeneratingTerm hq0 hq1 hw0 hw1).mul_left _
  have hW := hasSum_coeff_wsumG hw0 (coeff_outerTerm_nonneg hq0 hq1)
    (hasSum_outerTerm hq0 hq1 hw0 hw1) hsummable
  have hE2 : HasSum (fun n => coeff n (eER q ^ 2) * w ^ n)
      ((qPochhammerInfinity w q)⁻¹ * (qPochhammerInfinity w q)⁻¹) := by
    rw [pow_two]
    exact hasSum_coeff_mul hw0 (coeff_eER_nonneg hq0 hq1) (coeff_eER_nonneg hq0 hq1)
      (hasSum_eER hq0 hq1 hw0 hw1) (hasSum_eER hq0 hq1 hw0 hw1)
  have hE20 : ∀ n, 0 ≤ coeff n (eER q ^ 2) := by
    rw [pow_two]
    exact coeff_mul_nonneg (coeff_eER_nonneg hq0 hq1) (coeff_eER_nonneg hq0 hq1)
  have htot := hasSum_coeff_mul hw0 hE20 (coeff_wsumG_nonneg (coeff_outerTerm_nonneg hq0 hq1))
    hE2 hW
  rw [formB_real' hq0 hq1] at htot
  convert htot using 1
  · funext n
    rw [coeff_mk]
  · rw [tsum_congr (outer_value_eq hq0 hq1), tsum_mul_left]
    unfold actualGeneratingFunction
    have h3 := (PaperR10.qPochhammerInfinity_pos w q).ne'
    field_simp

end RealIdentity

/-! ### Bounds on the weights and the fixed-shift limit -/

section Bounds

variable {q : ℝ}

/-- `b^{(r)}_k = ∑_{n_1+⋯+n_r=k} ∏_j 1/(q;q)_{n_j}`, so that `R_k^{(r)} = (q;q)_k b^{(r)}_k`. -/
def realB (q : ℝ) (r k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Nat.antidiagonalTuple r k, ∏ j, (qPochhammerFinite q q (n j))⁻¹

lemma realRogersR_eq (r k : ℕ) : realRogersR r k q = qPochhammerFinite q q k * realB q r k := by
  rw [realRogersR, realB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_mul_inv, Finset.prod_inv_distrib]

lemma realGamma_eq (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    realGamma q k = qPochhammerFinite q q k * realB q 2 k * realB q 3 k := by
  have h := (qPochhammerFinite_q_pos hq0 hq1 k).ne'
  rw [realGamma, realRogersR_eq, realRogersR_eq]
  field_simp

lemma realB_two (k : ℕ) : realB q 2 k =
    ∑ i ∈ range (k + 1), (qPochhammerFinite q q i)⁻¹ * (qPochhammerFinite q q (k - i))⁻¹ := by
  rw [realB, sum_antidiagonalTuple_two, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_two]
  rfl

lemma realB_three (k : ℕ) : realB q 3 k =
    ∑ i ∈ range (k + 1), (qPochhammerFinite q q i)⁻¹ * realB q 2 (k - i) := by
  rw [realB, sum_antidiagonalTuple_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [realB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma one_le_einv (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 1 ≤ (qPochhammerFinite q q n)⁻¹ :=
  (one_le_inv₀ (qPochhammerFinite_q_pos hq0 hq1 n)).mpr (qPochhammerFinite_q_le_one hq0 hq1 n)

lemma einv_le (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (qPochhammerFinite q q n)⁻¹ ≤ (qPochhammerInfinity q q)⁻¹ :=
  inv_anti₀ (PaperR10.qPochhammerInfinity_pos q q) (P_le_qPochhammerFinite hq0 hq1 n)

lemma einv_mono (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (qPochhammerFinite q q n)⁻¹ ≤ (qPochhammerFinite q q (n + 1))⁻¹ := by
  apply inv_anti₀ (qPochhammerFinite_q_pos hq0 hq1 (n + 1))
  rw [PaperR10.qPochhammerFinite_succ]
  have hpos := qPochhammerFinite_q_pos hq0 hq1 n
  have h1 : 0 ≤ q * q ^ n := mul_nonneg hq0.le (pow_nonneg hq0.le n)
  nlinarith

lemma Pinv_ge_one (hq0 : 0 < q) (hq1 : q < 1) : 1 ≤ (qPochhammerInfinity q q)⁻¹ :=
  (one_le_einv hq0 hq1 0).trans (einv_le hq0 hq1 0)

lemma sum_range_id_succ (k : ℕ) :
    ∑ j ∈ range (k + 1), ((j : ℝ) + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

lemma sum_range_succ_cast (k : ℕ) :
    ∑ i ∈ range (k + 1), (((k - i : ℕ) : ℝ) + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by
  have h := Finset.sum_range_reflect (fun j : ℕ => ((j : ℝ) + 1)) (k + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h, sum_range_id_succ]

lemma realB_two_bounds (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    (k : ℝ) + 1 ≤ realB q 2 k ∧
      realB q 2 k ≤ ((k : ℝ) + 1) * ((qPochhammerInfinity q q)⁻¹) ^ 2 := by
  rw [realB_two]
  constructor
  · have h : ∑ i ∈ range (k + 1), (1 : ℝ) ≤ ∑ i ∈ range (k + 1),
        (qPochhammerFinite q q i)⁻¹ * (qPochhammerFinite q q (k - i))⁻¹ :=
      Finset.sum_le_sum fun i _ =>
        one_le_mul_of_one_le_of_one_le (one_le_einv hq0 hq1 i) (one_le_einv hq0 hq1 (k - i))
    simpa using h
  · have h : ∑ i ∈ range (k + 1),
        (qPochhammerFinite q q i)⁻¹ * (qPochhammerFinite q q (k - i))⁻¹ ≤
          ∑ i ∈ range (k + 1), ((qPochhammerInfinity q q)⁻¹) ^ 2 :=
      Finset.sum_le_sum fun i _ => by
        rw [pow_two]
        exact mul_le_mul (einv_le hq0 hq1 i) (einv_le hq0 hq1 (k - i))
          (inv_nonneg.mpr (qPochhammerFinite_q_pos hq0 hq1 _).le)
          (inv_nonneg.mpr (PaperR10.qPochhammerInfinity_pos q q).le)
    simpa using h

lemma realB_three_bounds (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 ≤ realB q 3 k ∧
      realB q 3 k ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * ((qPochhammerInfinity q q)⁻¹) ^ 3 := by
  rw [realB_three, ← sum_range_succ_cast, Finset.sum_mul]
  constructor
  · refine Finset.sum_le_sum fun i _ => ?_
    have h1 := one_le_einv hq0 hq1 i
    have h2 := (realB_two_bounds hq0 hq1 (k - i)).1
    have h3 : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) + 1 := by positivity
    nlinarith
  · refine Finset.sum_le_sum fun i _ => ?_
    have h1 := einv_le hq0 hq1 i
    have h1' := one_le_einv hq0 hq1 i
    have h2 := (realB_two_bounds hq0 hq1 (k - i)).2
    have h2' := (realB_two_bounds hq0 hq1 (k - i)).1
    have hP : 0 ≤ (qPochhammerInfinity q q)⁻¹ :=
      inv_nonneg.mpr (PaperR10.qPochhammerInfinity_pos q q).le
    calc (qPochhammerFinite q q i)⁻¹ * realB q 2 (k - i)
        ≤ (qPochhammerInfinity q q)⁻¹ *
            ((((k - i : ℕ) : ℝ) + 1) * ((qPochhammerInfinity q q)⁻¹) ^ 2) :=
          mul_le_mul h1 h2 (by linarith) hP
      _ = (((k - i : ℕ) : ℝ) + 1) * ((qPochhammerInfinity q q)⁻¹) ^ 3 := by ring

/-- `c_k = (k+1)^2 (k+2)/2`. -/
def cK (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2

lemma cK_pos (k : ℕ) : 0 < cK k := by unfold cK; positivity

lemma realGamma_bounds (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    qPochhammerInfinity q q * cK k ≤ realGamma q k ∧
      realGamma q k ≤ ((qPochhammerInfinity q q)⁻¹) ^ 5 * cK k := by
  rw [realGamma_eq hq0 hq1]
  have hP := PaperR10.qPochhammerInfinity_pos q q
  have hA0 := qPochhammerFinite_q_pos hq0 hq1 k
  have hA1 := qPochhammerFinite_q_le_one hq0 hq1 k
  have hA2 := P_le_qPochhammerFinite hq0 hq1 k
  obtain ⟨hB1, hB2⟩ := realB_two_bounds hq0 hq1 k
  obtain ⟨hD1, hD2⟩ := realB_three_bounds hq0 hq1 k
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by positivity
  unfold cK
  constructor
  · calc qPochhammerInfinity q q * (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2)
        = qPochhammerInfinity q q * ((k : ℝ) + 1) * (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) := by
          ring
      _ ≤ qPochhammerFinite q q k * realB q 2 k * realB q 3 k := by
          apply mul_le_mul (mul_le_mul hA2 hB1 hk1 hA0.le) hD1 hk2
          exact mul_nonneg hA0.le (hk1.trans hB1)
  · have hPi : 0 ≤ (qPochhammerInfinity q q)⁻¹ := inv_nonneg.mpr hP.le
    calc qPochhammerFinite q q k * realB q 2 k * realB q 3 k
        ≤ 1 * (((k : ℝ) + 1) * ((qPochhammerInfinity q q)⁻¹) ^ 2) *
            (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * ((qPochhammerInfinity q q)⁻¹) ^ 3) := by
          apply mul_le_mul (mul_le_mul hA1 hB2 (hk1.trans hB1) zero_le_one) hD2
            (hk2.trans hD1)
          positivity
      _ = ((qPochhammerInfinity q q)⁻¹) ^ 5 * (((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2) := by
          ring

lemma cK_shift_le (k h : ℕ) : cK (k + h) ≤ (1 + (h : ℝ)) ^ 3 * cK k := by
  unfold cK
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have e1 : (k : ℝ) + h + 1 ≤ (1 + h) * ((k : ℝ) + 1) := by nlinarith
  have e2 : (k : ℝ) + h + 2 ≤ (1 + h) * ((k : ℝ) + 2) := by nlinarith
  have e1' : ((k : ℝ) + h + 1) ^ 2 ≤ ((1 + h) * ((k : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e1 2
  have := mul_le_mul e1' e2 (by positivity) (by positivity)
  nlinarith

/-- The fixed-shift ratio of a sequence with small relative increments tends to one. -/
lemma tendsto_succ_ratio {b : ℕ → ℝ} (M : ℝ) (hb : ∀ k, 0 < b k)
    (hinc0 : ∀ k, b k ≤ b (k + 1)) (hinc : ∀ k, b (k + 1) - b k ≤ M * b k / ((k : ℝ) + 1)) :
    Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 1) := by
  have hup : Tendsto (fun k : ℕ => 1 + M * (1 / ((k : ℝ) + 1))) atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul M
    simpa using this.const_add 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_) (fun k => ?_)
  · exact (one_le_div (hb k)).mpr (hinc0 k)
  · have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_le_iff₀ (hb k)]
    have := hinc k
    rw [le_div_iff₀ hk] at this
    have e : (1 + M * (1 / ((k : ℝ) + 1))) * b k * ((k : ℝ) + 1) =
        b k * ((k : ℝ) + 1) + M * b k := by field_simp
    nlinarith [e]

lemma tendsto_shift_ratio {b : ℕ → ℝ} (hb : ∀ k, 0 < b k)
    (h1 : Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 1)) (h : ℕ) :
    Tendsto (fun k => b (k + h) / b k) atTop (𝓝 1) := by
  induction h with
  | zero =>
      simp only [Nat.add_zero]
      refine tendsto_const_nhds.congr fun k => ?_
      rw [div_self (hb k).ne']
  | succ h ih =>
      have hc : Tendsto (fun k => b (k + h + 1) / b (k + h)) atTop (𝓝 1) :=
        h1.comp (tendsto_add_atTop_nat h)
      have := hc.mul ih
      rw [one_mul] at this
      refine this.congr fun k => ?_
      rw [← add_assoc]
      field_simp [(hb (k + h)).ne', (hb k).ne']

lemma realB_two_pos (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) : 0 < realB q 2 k :=
  lt_of_lt_of_le (by positivity) (realB_two_bounds hq0 hq1 k).1

lemma realB_three_pos (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) : 0 < realB q 3 k :=
  lt_of_lt_of_le (by positivity) (realB_three_bounds hq0 hq1 k).1

lemma realB_two_increment (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ realB q 2 (k + 1) - realB q 2 k ∧
      realB q 2 (k + 1) - realB q 2 k ≤ 2 * ((qPochhammerInfinity q q)⁻¹) ^ 2 := by
  set e : ℕ → ℝ := fun n => (qPochhammerFinite q q n)⁻¹ with he
  have hdiff : realB q 2 (k + 1) - realB q 2 k =
      ∑ i ∈ range (k + 1), e i * (e (k + 1 - i) - e (k - i)) + e (k + 1) * e 0 := by
    rw [realB_two, realB_two, Finset.sum_range_succ, Nat.sub_self]
    simp only [he, mul_sub, Finset.sum_sub_distrib]
    ring
  have hmono : ∀ i ∈ range (k + 1), e (k - i) ≤ e (k + 1 - i) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [show k + 1 - i = (k - i) + 1 by omega]
    exact einv_mono hq0 hq1 (k - i)
  have htel : ∑ i ∈ range (k + 1), (e (k + 1 - i) - e (k - i)) = e (k + 1) - e 0 := by
    have h := Finset.sum_range_reflect (fun j => e (j + 1) - e j) (k + 1)
    rw [Finset.sum_range_sub] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [show k + 1 - 1 - i + 1 = k + 1 - i by omega, show k + 1 - 1 - i = k - i by omega]
  have he0 : e 0 = 1 := by simp [he]
  have hPi := Pinv_ge_one hq0 hq1
  have he_le : ∀ n, e n ≤ (qPochhammerInfinity q q)⁻¹ := fun n => einv_le hq0 hq1 n
  have he_ge : ∀ n, 1 ≤ e n := fun n => one_le_einv hq0 hq1 n
  rw [hdiff]
  constructor
  · have h1 : 0 ≤ ∑ i ∈ range (k + 1), e i * (e (k + 1 - i) - e (k - i)) :=
      Finset.sum_nonneg fun i hi => mul_nonneg (by linarith [he_ge i]) (by linarith [hmono i hi])
    have h2 : 0 ≤ e (k + 1) * e 0 := mul_nonneg (by linarith [he_ge (k + 1)]) (by linarith [he_ge 0])
    linarith
  · have h1 : ∑ i ∈ range (k + 1), e i * (e (k + 1 - i) - e (k - i)) ≤
        (qPochhammerInfinity q q)⁻¹ * (e (k + 1) - e 0) := by
      rw [← htel, Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (he_le i) (by linarith [hmono i hi])
    have h2 : e (k + 1) - e 0 ≤ (qPochhammerInfinity q q)⁻¹ := by
      linarith [he_le (k + 1), he_ge 0]
    have h3 : e (k + 1) * e 0 ≤ (qPochhammerInfinity q q)⁻¹ := by
      rw [he0, mul_one]; exact he_le (k + 1)
    nlinarith

lemma realB_three_increment (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ realB q 3 (k + 1) - realB q 3 k ∧
      realB q 3 (k + 1) - realB q 3 k ≤ 3 * ((k : ℝ) + 1) * ((qPochhammerInfinity q q)⁻¹) ^ 3 := by
  set e : ℕ → ℝ := fun n => (qPochhammerFinite q q n)⁻¹ with he
  have hdiff : realB q 3 (k + 1) - realB q 3 k =
      ∑ i ∈ range (k + 1), e i * (realB q 2 (k + 1 - i) - realB q 2 (k - i)) +
        e (k + 1) * realB q 2 0 := by
    rw [realB_three, realB_three, Finset.sum_range_succ, Nat.sub_self]
    simp only [he, mul_sub, Finset.sum_sub_distrib]
    ring
  have hB20 : realB q 2 0 = 1 := by simp [realB_two]
  have hPi := Pinv_ge_one hq0 hq1
  have he_le : ∀ n, e n ≤ (qPochhammerInfinity q q)⁻¹ := fun n => einv_le hq0 hq1 n
  have he_ge : ∀ n, 1 ≤ e n := fun n => one_le_einv hq0 hq1 n
  have hinc : ∀ i ∈ range (k + 1), 0 ≤ realB q 2 (k + 1 - i) - realB q 2 (k - i) ∧
      realB q 2 (k + 1 - i) - realB q 2 (k - i) ≤ 2 * ((qPochhammerInfinity q q)⁻¹) ^ 2 := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [show k + 1 - i = (k - i) + 1 by omega]
    exact realB_two_increment hq0 hq1 (k - i)
  rw [hdiff, hB20, mul_one]
  constructor
  · have h1 : 0 ≤ ∑ i ∈ range (k + 1), e i * (realB q 2 (k + 1 - i) - realB q 2 (k - i)) :=
      Finset.sum_nonneg fun i hi => mul_nonneg (by linarith [he_ge i]) (hinc i hi).1
    linarith [he_ge (k + 1)]
  · have h1 : ∑ i ∈ range (k + 1), e i * (realB q 2 (k + 1 - i) - realB q 2 (k - i)) ≤
        ∑ i ∈ range (k + 1), (qPochhammerInfinity q q)⁻¹ * (2 * ((qPochhammerInfinity q q)⁻¹) ^ 2) :=
      Finset.sum_le_sum fun i hi => mul_le_mul (he_le i) (hinc i hi).2 (hinc i hi).1
        (by linarith)
    rw [Finset.sum_const, card_range, nsmul_eq_mul] at h1
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hP3 : (qPochhammerInfinity q q)⁻¹ ≤ ((qPochhammerInfinity q q)⁻¹) ^ 3 := by
      nlinarith [hPi]
    push_cast at h1
    have hPk : (qPochhammerInfinity q q)⁻¹ ≤ ((k : ℝ) + 1) * ((qPochhammerInfinity q q)⁻¹) ^ 3 := by
      nlinarith [hP3, hk]
    nlinarith [he_le (k + 1)]

lemma tendsto_realB_two_ratio (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun k => realB q 2 (k + 1) / realB q 2 k) atTop (𝓝 1) := by
  refine tendsto_succ_ratio (2 * ((qPochhammerInfinity q q)⁻¹) ^ 2) (realB_two_pos hq0 hq1)
    (fun k => by linarith [(realB_two_increment hq0 hq1 k).1]) (fun k => ?_)
  have h := (realB_two_increment hq0 hq1 k).2
  have hb := (realB_two_bounds hq0 hq1 k).1
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hk]
  have hM : 0 ≤ 2 * ((qPochhammerInfinity q q)⁻¹) ^ 2 := by positivity
  nlinarith

lemma tendsto_realB_three_ratio (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun k => realB q 3 (k + 1) / realB q 3 k) atTop (𝓝 1) := by
  refine tendsto_succ_ratio (6 * ((qPochhammerInfinity q q)⁻¹) ^ 3) (realB_three_pos hq0 hq1)
    (fun k => by linarith [(realB_three_increment hq0 hq1 k).1]) (fun k => ?_)
  have h := (realB_three_increment hq0 hq1 k).2
  have hb := (realB_three_bounds hq0 hq1 k).1
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hk]
  have hM : 0 ≤ ((qPochhammerInfinity q q)⁻¹) ^ 3 :=
    pow_nonneg (inv_nonneg.mpr (PaperR10.qPochhammerInfinity_pos q q).le) 3
  have hk2 : ((k : ℝ) + 1) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by nlinarith
  nlinarith

lemma tendsto_qPochhammerFinite_shift_ratio (hq0 : 0 < q) (hq1 : q < 1) (h : ℕ) :
    Tendsto (fun k => qPochhammerFinite q q (k + h) / qPochhammerFinite q q k) atTop (𝓝 1) := by
  have hT := PaperR10.tendsto_qPochhammerFinite hq0.le hq1 hq0.le hq1
  have hP := (PaperR10.qPochhammerInfinity_pos q q).ne'
  have := (hT.comp (tendsto_add_atTop_nat h)).div hT hP
  rw [div_self hP] at this
  exact this

/-- For each fixed `h`, `a_{k+h}/a_k → 1`, with `a_k = P^4 γ_k`. -/
lemma tendsto_weight_ratio (hq0 : 0 < q) (hq1 : q < 1) (h : ℕ) :
    Tendsto (fun k => qPochhammerInfinity q q ^ 4 * realGamma q (k + h) /
      (qPochhammerInfinity q q ^ 4 * realGamma q k)) atTop (𝓝 1) := by
  have h1 := tendsto_qPochhammerFinite_shift_ratio hq0 hq1 h
  have h2 := tendsto_shift_ratio (realB_two_pos hq0 hq1) (tendsto_realB_two_ratio hq0 hq1) h
  have h3 := tendsto_shift_ratio (realB_three_pos hq0 hq1) (tendsto_realB_three_ratio hq0 hq1) h
  have := (h1.mul h2).mul h3
  rw [one_mul, one_mul] at this
  refine this.congr fun k => ?_
  have hP := (PaperR10.qPochhammerInfinity_pos q q).ne'
  have hA := (qPochhammerFinite_q_pos hq0 hq1 k).ne'
  have hB := (realB_two_pos hq0 hq1 k).ne'
  have hD := (realB_three_pos hq0 hq1 k).ne'
  rw [realGamma_eq hq0 hq1, realGamma_eq hq0 hq1]
  field_simp

end Bounds

/-! ### Weights, uniqueness of coefficients, specialisation -/

section Assembly

variable {q : ℝ}

lemma weight_bounds (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    qPochhammerInfinity q q ^ 5 * cK k ≤ qPochhammerInfinity q q ^ 4 * realGamma q k ∧
      qPochhammerInfinity q q ^ 4 * realGamma q k ≤ (qPochhammerInfinity q q)⁻¹ * cK k := by
  obtain ⟨h1, h2⟩ := realGamma_bounds hq0 hq1 k
  have hP := PaperR10.qPochhammerInfinity_pos q q
  constructor
  · calc qPochhammerInfinity q q ^ 5 * cK k
        = qPochhammerInfinity q q ^ 4 * (qPochhammerInfinity q q * cK k) := by ring
      _ ≤ qPochhammerInfinity q q ^ 4 * realGamma q k :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  · calc qPochhammerInfinity q q ^ 4 * realGamma q k
        ≤ qPochhammerInfinity q q ^ 4 * (((qPochhammerInfinity q q)⁻¹) ^ 5 * cK k) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (qPochhammerInfinity q q)⁻¹ * cK k := by
          field_simp

lemma weight_pos (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 < qPochhammerInfinity q q ^ 4 * realGamma q k := by
  have hP := PaperR10.qPochhammerInfinity_pos q q
  have := cK_pos k
  exact lt_of_lt_of_le (by positivity) (weight_bounds hq0 hq1 k).1

lemma weight_ratio_le (hq0 : 0 < q) (hq1 : q < 1) (k h : ℕ) :
    qPochhammerInfinity q q ^ 4 * realGamma q (k + h) /
        (qPochhammerInfinity q q ^ 4 * realGamma q k) ≤
      ((qPochhammerInfinity q q)⁻¹) ^ 6 * (1 + (h : ℝ)) ^ 3 := by
  have hb1 := weight_bounds hq0 hq1 (k + h)
  have hb2 := weight_bounds hq0 hq1 k
  have hP := PaperR10.qPochhammerInfinity_pos q q
  have hc := cK_pos k
  have hh : (0 : ℝ) ≤ 1 + (h : ℝ) := by positivity
  rw [div_le_iff₀ (weight_pos hq0 hq1 k)]
  calc qPochhammerInfinity q q ^ 4 * realGamma q (k + h)
      ≤ (qPochhammerInfinity q q)⁻¹ * cK (k + h) := hb1.2
    _ ≤ (qPochhammerInfinity q q)⁻¹ * ((1 + (h : ℝ)) ^ 3 * cK k) :=
        mul_le_mul_of_nonneg_left (cK_shift_le k h) (inv_nonneg.mpr hP.le)
    _ = ((qPochhammerInfinity q q)⁻¹) ^ 6 * (1 + (h : ℝ)) ^ 3 *
          (qPochhammerInfinity q q ^ 5 * cK k) := by
        field_simp
    _ ≤ ((qPochhammerInfinity q q)⁻¹) ^ 6 * (1 + (h : ℝ)) ^ 3 *
          (qPochhammerInfinity q q ^ 4 * realGamma q k) :=
        mul_le_mul_of_nonneg_left hb2.1 (by positivity)

/-- A power series vanishing on `[0,1)` has zero coefficients. -/
lemma coeff_zero_of_hasSum_zero {e : ℕ → ℝ}
    (he : ∀ w, 0 ≤ w → w < 1 → HasSum (fun n => e n * w ^ n) 0) : ∀ n, e n = 0 := by
  have hconv := (he (3 / 4) (by norm_num) (by norm_num)).summable
  obtain ⟨M, hM⟩ : ∃ M, ∀ n, ‖e n * (3 / 4 : ℝ) ^ n‖ ≤ M := by
    have hb := Metric.isBounded_range_of_tendsto _ hconv.tendsto_atTop_zero
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
    exact ⟨M, fun n => hM _ ⟨n, rfl⟩⟩
  have hbd : ∀ m, |e m| ≤ M * (4 / 3 : ℝ) ^ m := by
    intro m
    have h := hM m
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (3 / 4) ^ m)] at h
    have h34 : (0 : ℝ) < (3 / 4 : ℝ) ^ m := by positivity
    have e1 : (4 / 3 : ℝ) ^ m * (3 / 4 : ℝ) ^ m = 1 := by
      rw [← mul_pow]; norm_num
    calc |e m| = |e m| * ((3 / 4 : ℝ) ^ m * (4 / 3 : ℝ) ^ m) := by rw [mul_comm ((3/4 : ℝ) ^ m), e1, mul_one]
      _ = (|e m| * (3 / 4 : ℝ) ^ m) * (4 / 3 : ℝ) ^ m := by ring
      _ ≤ M * (4 / 3 : ℝ) ^ m := mul_le_mul_of_nonneg_right h (by positivity)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hshift : ∀ w, 0 < w → w < 1 → HasSum (fun i => e (i + n) * w ^ i) 0 := by
      intro w hw0 hw1
      have h := he w hw0.le hw1
      have h2 := (hasSum_nat_add_iff' n).mpr h
      have hz : ∑ i ∈ range n, e i * w ^ i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [ih i (mem_range.mp hi), zero_mul]
      rw [hz, sub_zero] at h2
      have h3 := h2.mul_left (w ^ n)⁻¹
      rw [mul_zero] at h3
      convert h3 using 1
      funext i
      have hwn : w ^ n ≠ 0 := pow_ne_zero n hw0.ne'
      rw [pow_add]
      field_simp
    have hlim : Tendsto (fun w : ℝ => ∑' i, e (i + n) * w ^ i) (𝓝[>] 0)
        (𝓝 (∑' i : ℕ, if i = 0 then e n else 0)) := by
      refine tendsto_tsum_of_dominated_convergence
        (bound := fun i => M * (4 / 3 : ℝ) ^ n * (2 / 3 : ℝ) ^ i)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _) (fun i => ?_) ?_
      · have hc : Tendsto (fun w : ℝ => e (i + n) * w ^ i) (𝓝 0) (𝓝 (e (i + n) * 0 ^ i)) :=
          ((continuous_pow i).tendsto 0).const_mul _
        have h0 : e (i + n) * (0 : ℝ) ^ i = if i = 0 then e n else 0 := by
          rcases Nat.eq_zero_or_pos i with rfl | hi
          · simp
          · rw [zero_pow hi.ne', mul_zero, if_neg hi.ne']
        rw [h0] at hc
        exact tendsto_nhdsWithin_of_tendsto_nhds hc
      · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with w hw i
        obtain ⟨hw0, hw1⟩ := hw
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hw0 i)]
        have h1 := hbd (i + n)
        have h2 : w ^ i ≤ (1 / 2 : ℝ) ^ i := pow_le_pow_left₀ hw0.le hw1.le i
        calc |e (i + n)| * w ^ i ≤ M * (4 / 3 : ℝ) ^ (i + n) * (1 / 2 : ℝ) ^ i :=
              mul_le_mul h1 h2 (pow_nonneg hw0.le i) ((abs_nonneg _).trans h1)
          _ = M * (4 / 3 : ℝ) ^ n * (2 / 3 : ℝ) ^ i := by
              rw [pow_add, show (2 / 3 : ℝ) = (4 / 3) * (1 / 2) by norm_num, mul_pow]
              ring
    rw [tsum_ite_eq] at hlim
    have hev : ∀ᶠ w in 𝓝[>] (0 : ℝ), (fun w => ∑' i, e (i + n) * w ^ i) w = 0 := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with w hw
      exact (hshift w hw.1 hw.2).tsum_eq
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm))

/-- Uniqueness of the coefficients of a power series on `[0,1)`. -/
lemma eq_of_hasSum_on_unit_interval {c d : ℕ → ℝ} {F : ℝ → ℝ}
    (hc : ∀ w, 0 ≤ w → w < 1 → HasSum (fun n => c n * w ^ n) (F w))
    (hd : ∀ w, 0 ≤ w → w < 1 → HasSum (fun n => d n * w ^ n) (F w)) : c = d := by
  have he : ∀ w, 0 ≤ w → w < 1 → HasSum (fun n => (c n - d n) * w ^ n) 0 := by
    intro w hw0 hw1
    have h := (hc w hw0 hw1).sub (hd w hw0 hw1)
    rw [sub_self] at h
    convert h using 1
    funext n
    ring
  funext n
  exact sub_eq_zero.mp (coeff_zero_of_hasSum_zero he n)

/-- The formal `γ_k ∈ ℚ⟦q⟧` converges at the real point `q` to `R_k^{(2)}(q)R_k^{(3)}(q)/(q;q)_k`. -/
lemma hasSum_momentWeight_at (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    HasSum (fun m => ((coeff m (momentWeight k) : ℚ) : ℝ) * q ^ m) (realGamma q k) := by
  have hval : momentWeight k = (absConv q).subtype (rogersA hq0.le hq1 k) := by
    rw [rogersA_val, momentWeight_eq, ifac]
  have h := hasSum_evq q (rogersA hq0.le hq1 k)
  rw [evq_rogersA] at h
  rw [hval]
  exact h

/-- Integer polynomials as elements of the subring. -/
def polyA (q : ℝ) : Polynomial ℤ →+* absConv q := Polynomial.eval₂RingHom (Int.castRingHom _) (qA q)

lemma subtype_polyA (p : Polynomial ℤ) : (absConv q).subtype (polyA q p) = toQSeries p := by
  have hext : ((absConv q).subtype).comp (polyA q) = toQSeries := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · exact RingHom.congr_fun (RingHom.ext_int ((((absConv q).subtype).comp (polyA q)).comp
        Polynomial.C) (toQSeries.comp Polynomial.C)) a
    · rw [RingHom.comp_apply, toQSeries_X, polyA, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      rfl
  exact RingHom.congr_fun hext p

lemma evq_polyA (p : Polynomial ℤ) : evq q (polyA q p) = p.eval₂ (Int.castRingHom ℝ) q := by
  have hext : (evq q).comp (polyA q) = Polynomial.eval₂RingHom (Int.castRingHom ℝ) q := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · exact RingHom.congr_fun (RingHom.ext_int (((evq q).comp (polyA q)).comp Polynomial.C)
        ((Polynomial.eval₂RingHom (Int.castRingHom ℝ) q).comp Polynomial.C)) a
    · rw [RingHom.comp_apply, polyA, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evq_qA]
  exact RingHom.congr_fun hext p

lemma realRogersR_two_eval (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    realRogersR 2 k q = (rogersPoly2 k).eval₂ (Int.castRingHom ℝ) q := by
  have h : R2A hq0 hq1 k = polyA q (rogersPoly2 k) :=
    Subtype.val_injective (by
      change (absConv q).subtype (R2A hq0 hq1 k) = (absConv q).subtype (polyA q (rogersPoly2 k))
      rw [R2A_val, subtype_polyA, toQSeries_rogersPoly2])
  rw [← evq_R2A hq0 hq1, h, evq_polyA]

lemma realRogersR_three_eval (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    realRogersR 3 k q = (rogersPoly3 k).eval₂ (Int.castRingHom ℝ) q := by
  have h : R3A hq0 hq1 k = polyA q (rogersPoly3 k) :=
    Subtype.val_injective (by
      change (absConv q).subtype (R3A hq0 hq1 k) = (absConv q).subtype (polyA q (rogersPoly3 k))
      rw [R3A_val, subtype_polyA, toQSeries_rogersPoly3])
  rw [← evq_R3A hq0 hq1, h, evq_polyA]

end Assembly

/-- `long1049:prop:rogers-factorisation`: the moment weights as a product of two finite sums,
every clause of the proposition.

*Formal clauses* (`q` an indeterminate; `rogers_factorisation`): with
`R_k^{(r)}(q) = ∑_{n_1+⋯+n_r=k} (q;q)_k / ∏_{j ≤ r} (q;q)_{n_j}` and
`γ_k(q) = [w^k] G_q(w)` computed from
`G_q(w) = (w;q)_∞^{-3} ∑_{t ≥ 0} w^t/(q;q)_t · (q^t w^2;q)_∞/(q^t w;q)_∞^2` in `ℚ⟦q⟧⟦w⟧`,
one has `γ_k = R_k^{(2)} R_k^{(3)} / (q;q)_k`; the product `R_k^{(2)} R_k^{(3)}` lies in
`ℤ_{≥0}[q]`, has degree `⌊k²/4⌋ + ⌊k²/3⌋` and coefficient sum `6^k`; and
`(q;q)_k γ_k ∈ ℤ[q]`.

*Real clauses* (fixed `0 < q < 1`, the paper's setting): `G_q(w)` is the tree's
`actualGeneratingFunction q w` (the same formula with genuine real infinite products), and
`γ_k = [w^k] G_q(w)` is its coefficient sequence on `[0,1)`.  That sequence exists and is
unique, equal to `R_k^{(2)}(q) R_k^{(3)}(q) / (q;q)_k`; the formal `γ_k ∈ ℚ⟦q⟧` converges at
`q` to it; `R_k^{(2)}, R_k^{(3)}` are the integer polynomials evaluated at `q`, and so is
`(q;q)_k γ_k`.  With `P = (q;q)_∞`, `c_k = (k+1)^2 (k+2)/2` and `a_k = P^4 γ_k`:
`P^5 c_k ≤ a_k ≤ P^{-1} c_k` for all `k ≥ 0`, `a_{k+h}/a_k ≤ P^{-6} (1+h)^3`, and the
hypotheses of `long1049:thm:geometric-universality` hold with `C = P^{-6}` and `κ = 3`:
`a_k > 0`, `a_{k+h}/a_k → 1` for each fixed `h`, and the ratio bound. -/
theorem rogers_factorisation_proposition :
    (∀ k : ℕ,
      momentWeight k = rogersR 2 k * rogersR 3 k * (qfac k)⁻¹ ∧
      qfac k * momentWeight k = rogersR 2 k * rogersR 3 k ∧
      (∃ p : Polynomial ℕ,
        ((p.map (Nat.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
          rogersR 2 k * rogersR 3 k ∧
        p.natDegree = k ^ 2 / 4 + k ^ 2 / 3 ∧
        p.eval 1 = 6 ^ k) ∧
      (∃ g : Polynomial ℤ,
        qfac k * momentWeight k =
          ((g.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ))) ∧
    (∀ q : ℝ, 0 < q → q < 1 →
      (∀ w : ℝ, 0 ≤ w → w < 1 →
        HasSum (fun k => realRogersR 2 k q * realRogersR 3 k q / qPochhammerFinite q q k * w ^ k)
          (actualGeneratingFunction q w)) ∧
      ∀ γ : ℕ → ℝ, (∀ w : ℝ, 0 ≤ w → w < 1 →
          HasSum (fun k => γ k * w ^ k) (actualGeneratingFunction q w)) →
        (∀ k, γ k = realRogersR 2 k q * realRogersR 3 k q / qPochhammerFinite q q k) ∧
        (∀ k, HasSum (fun m => ((coeff m (momentWeight k) : ℚ) : ℝ) * q ^ m) (γ k)) ∧
        (∀ k, realRogersR 2 k q = (rogersPoly2 k).eval₂ (Int.castRingHom ℝ) q ∧
          realRogersR 3 k q = (rogersPoly3 k).eval₂ (Int.castRingHom ℝ) q ∧
          qPochhammerFinite q q k * γ k =
            (rogersPoly2 k * rogersPoly3 k).eval₂ (Int.castRingHom ℝ) q) ∧
        (∀ k, qPochhammerInfinity q q ^ 5 * cK k ≤ qPochhammerInfinity q q ^ 4 * γ k ∧
          qPochhammerInfinity q q ^ 4 * γ k ≤ (qPochhammerInfinity q q)⁻¹ * cK k) ∧
        (∀ k h : ℕ, qPochhammerInfinity q q ^ 4 * γ (k + h) / (qPochhammerInfinity q q ^ 4 * γ k)
          ≤ ((qPochhammerInfinity q q)⁻¹) ^ 6 * (1 + (h : ℝ)) ^ 3) ∧
        (∀ k, 0 < qPochhammerInfinity q q ^ 4 * γ k) ∧
        (∀ h : ℕ, Tendsto (fun k => qPochhammerInfinity q q ^ 4 * γ (k + h) /
          (qPochhammerInfinity q q ^ 4 * γ k)) atTop (𝓝 1))) := by
  refine ⟨fun k => rogers_factorisation k, fun q hq0 hq1 => ⟨fun w hw0 hw1 => ?_, fun γ hγ => ?_⟩⟩
  · exact hasSum_realGamma hq0 hq1 hw0 hw1
  · have hγeq : γ = realGamma q := eq_of_hasSum_on_unit_interval hγ
      (fun w hw0 hw1 => hasSum_realGamma hq0 hq1 hw0 hw1)
    subst hγeq
    refine ⟨fun k => rfl, fun k => hasSum_momentWeight_at hq0 hq1 k, fun k => ⟨?_, ?_, ?_⟩,
      fun k => weight_bounds hq0 hq1 k, fun k h => weight_ratio_le hq0 hq1 k h,
      fun k => weight_pos hq0 hq1 k, fun h => tendsto_weight_ratio hq0 hq1 h⟩
    · exact realRogersR_two_eval hq0.le hq1 k
    · exact realRogersR_three_eval hq0.le hq1 k
    · have hA := (qPochhammerFinite_q_pos hq0 hq1 k).ne'
      rw [Polynomial.eval₂_mul, ← realRogersR_two_eval hq0.le hq1, ← realRogersR_three_eval hq0.le hq1,
        realGamma]
      field_simp

end ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogers_factorisation_proposition
