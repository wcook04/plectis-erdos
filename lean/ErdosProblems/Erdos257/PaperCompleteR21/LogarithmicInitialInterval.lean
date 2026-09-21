import ErdosProblems.Erdos257.PaperCompleteR8.KernelRecurrence
import ErdosProblems.Erdos257.CoverIndependentPeriodicMean

/-!
# Ordinary initial intervals for the shifted potential (long #257, line 9410)

Paper-form transcription of the long Erdős #257 `prop` "ordinary initial
intervals" at `paper/reasoning-parts/erdos257/a257_front.tex:9410`, together
with the objects of the section "Logarithmic cost under arithmetic sampling"
(lines 9177-9192) that the statement quantifies over.

For a finite nonempty `F ⊆ ℕ_{>0}` the paper writes

* `Q = lcm F` (`frameLcm`),
* `f_F(n) = #{a ∈ F : a ∣ n}` (`incidenceCount`),
* `U_F(N) = ∑_{r ≥ 1} 2^{-r} f_F(N+r) = ∑_{a ∈ F} 2^{N mod a}/(2^a - 1)`, which
  is the tree's `ErdosProblems.Erdos257.PaperCompleteR8.framePotential` (that is
  the second displayed form); the first displayed form is proved equal to it in
  `framePotential_eq_tsum` below,
* `κ₁(F;t) = min { ∑_{d ∣ Q} c_d/d : c_d ≥ 0 and
  log(1 + f_F(s)/t) ≤ ∑_{d ∣ s} c_d for every s ∣ Q }` (`kappaOne`).  The
  paper's `min` over its finite feasible programme is transcribed as the
  infimum of exactly that set of costs.

The proposition asserts, for every finite nonempty `F`, every integer `X ≥ 1`
and every `0 < t ≤ 1`,

  `#{1 ≤ N ≤ X : U_F(N) > t} / X ≤ (2 / log(4/3)) · κ₁(F;t)`.

The proof is the paper's.  A positive logarithmic divisor majorant `g` of cost
`K`; the geometric identity `∑_{r ≥ 1} 2^{-r}((4/3)^r - 1) = 1`, which forces a
shifted incidence above the budget whenever `U_F(N) > t`; the witness bound
`n < 2N ≤ 2X` in the regime `K < a/2` and a trivial bound otherwise; the fibre
bound `g(n)/a`; and `∑_{n ≤ 2X} g(n) ≤ 2KX`, which is the tree's
`ErdosProblems.Erdos257.cesaro_le_divisorMajorantCost`.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset
open ErdosProblems.Erdos257.PaperCompleteR8

/-- The paper's divisor-incidence count `f_F(n) = #{a ∈ F : a ∣ n}`. -/
def incidenceCount (F : Finset ℕ) (n : ℕ) : ℕ := (F.filter (fun a => a ∣ n)).card

/-- The paper's modulus `Q = lcm F`. -/
def frameLcm (F : Finset ℕ) : ℕ := F.lcm id

theorem frameLcm_ne_zero {F : Finset ℕ} (hF : 0 ∉ F) : frameLcm F ≠ 0 := by
  intro h
  obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h
  have hx0' : x = 0 := hx0
  exact hF (hx0' ▸ hx)

theorem dvd_frameLcm {F : Finset ℕ} {a : ℕ} (ha : a ∈ F) : a ∣ frameLcm F :=
  Finset.dvd_lcm ha

/-! ### Positive divisor majorants -/

/-- The value at `n` of the positive divisor majorant with coefficients `c`
supported on `D`: the paper's `g(n) = ∑_{d ∣ n} c_d`, with `c_d = 0` off `D`. -/
def divisorMajorant (D : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ D.filter (fun d => d ∣ n), c d

theorem divisorMajorant_nonneg {D : Finset ℕ} {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) (n : ℕ) :
    0 ≤ divisorMajorant D c n :=
  Finset.sum_nonneg fun d _ => hc d

theorem divisorMajorantCost_nonneg {D : Finset ℕ} {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d) :
    0 ≤ divisorMajorantCost D c := by
  unfold divisorMajorantCost
  exact Finset.sum_nonneg fun d _ => div_nonneg (hc d) (Nat.cast_nonneg d)

/-- The paper's `g(n) ≤ K n`. -/
theorem divisorMajorant_le_cost_mul {D : Finset ℕ} {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d)
    (hD : ∀ d ∈ D, 0 < d) {n : ℕ} (hn : 0 < n) :
    divisorMajorant D c n ≤ divisorMajorantCost D c * (n : ℝ) := by
  have hterm : ∀ d ∈ D.filter (fun d => d ∣ n), c d ≤ c d / (d : ℝ) * (n : ℝ) := by
    intro d hd
    obtain ⟨hdD, hdn⟩ := Finset.mem_filter.mp hd
    have hd0 : 0 < d := hD d hdD
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdle : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_dvd hn hdn
    have h1 : c d / (d : ℝ) * (d : ℝ) ≤ c d / (d : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hdle (div_nonneg (hc d) hdR.le)
    have h2 : c d / (d : ℝ) * (d : ℝ) = c d := by field_simp
    linarith
  calc divisorMajorant D c n
      ≤ ∑ d ∈ D.filter (fun d => d ∣ n), c d / (d : ℝ) * (n : ℝ) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ d ∈ D, c d / (d : ℝ) * (n : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro d _ _
        exact mul_nonneg (div_nonneg (hc d) (Nat.cast_nonneg d)) (Nat.cast_nonneg n)
    _ = divisorMajorantCost D c * (n : ℝ) := by
        unfold divisorMajorantCost
        rw [Finset.sum_mul]

/-- The paper's `∑_{n = 1}^{Y} g(n) = ∑_{d ∣ Q} c_d ⌊Y/d⌋ ≤ K Y`. -/
theorem sum_divisorMajorant_le {D : Finset ℕ} {c : ℕ → ℝ} (hc : ∀ d, 0 ≤ c d)
    (hD : ∀ d ∈ D, 0 < d) {Y : ℕ} (hY : 0 < Y) :
    (∑ n ∈ Finset.Icc 1 Y, divisorMajorant D c n)
      ≤ divisorMajorantCost D c * (Y : ℝ) := by
  have h := cesaro_le_divisorMajorantCost (divisorMajorant D c) D c Y hY hD
    (fun d _ => hc d) (divisorMajorant_nonneg hc) (fun _ _ => le_rfl)
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  exact (div_le_iff₀ hYR).mp h

/-! ### The logarithmic cost `κ₁` -/

/-- The costs of the admissible positive logarithmic divisor majorants of
`(F, t)`: the feasible set of the paper's programme (display 9.185). -/
def logMajorantCosts (F : Finset ℕ) (t : ℝ) : Set ℝ :=
  {K : ℝ | ∃ c : ℕ → ℝ, (∀ d, 0 ≤ c d) ∧
    (∀ s ∈ (frameLcm F).divisors,
        Real.log (1 + (incidenceCount F s : ℝ) / t) ≤ ∑ d ∈ s.divisors, c d) ∧
    K = divisorMajorantCost (frameLcm F).divisors c}

/-- The paper's `κ₁(F;t)`. -/
def kappaOne (F : Finset ℕ) (t : ℝ) : ℝ := sInf (logMajorantCosts F t)

/-- The programme is feasible: `c_d = log(1 + f_F(d)/t)` is admissible. -/
theorem logMajorantCosts_nonempty (F : Finset ℕ) {t : ℝ} (ht : 0 < t) :
    (logMajorantCosts F t).Nonempty := by
  classical
  have hnn : ∀ d : ℕ, 0 ≤ Real.log (1 + (incidenceCount F d : ℝ) / t) := by
    intro d
    apply Real.log_nonneg
    have hd : (0 : ℝ) ≤ (incidenceCount F d : ℝ) / t :=
      div_nonneg (Nat.cast_nonneg _) ht.le
    linarith
  refine ⟨divisorMajorantCost (frameLcm F).divisors
      (fun d => Real.log (1 + (incidenceCount F d : ℝ) / t)),
    fun d => Real.log (1 + (incidenceCount F d : ℝ) / t), hnn, ?_, rfl⟩
  intro s hs
  have hs0 : s ∈ s.divisors :=
    Nat.mem_divisors_self s (Nat.pos_of_mem_divisors hs).ne'
  exact Finset.single_le_sum
    (f := fun d => Real.log (1 + (incidenceCount F d : ℝ) / t))
    (fun d _ => hnn d) hs0

/-! ### The shifted potential -/

/-- The exact finite expansion of the tree's shifted potential:
`U_F(N) = ∑_{r < n} 2^{-(r+1)} f_F(N+r+1) + 2^{-n} U_F(N+n)`. -/
theorem framePotential_eq_partial (F : Finset ℕ) (hF : 0 ∉ F) (N n : ℕ) :
    framePotential F N =
      (∑ r ∈ Finset.range n, (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ))
        + (1 / 2 : ℝ) ^ n * framePotential F (N + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hidx : N + (n + 1) = N + n + 1 := by omega
      have hstep := framePotential_step F hF (N + n)
      have hc : ((F.filter (fun a => a ∣ N + n + 1)).card : ℝ)
          = (incidenceCount F (N + n + 1) : ℝ) := rfl
      rw [hc] at hstep
      have hU : framePotential F (N + n) =
          ((incidenceCount F (N + n + 1) : ℝ) + framePotential F (N + n + 1)) / 2 := by
        linarith
      rw [hidx, Finset.sum_range_succ, ih, hU]
      ring

/-- The paper's first displayed form of `U_F`: the tree's `framePotential` is
the shifted dyadic incidence series `∑_{r ≥ 1} 2^{-r} f_F(N+r)`. -/
theorem framePotential_eq_tsum (F : Finset ℕ) (hF : 0 ∉ F) (N : ℕ) :
    framePotential F N
      = ∑' r : ℕ, (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ) := by
  have hnn : ∀ r : ℕ, 0 ≤ (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ) := by
    intro r; positivity
  have heq : ∀ n : ℕ,
      (∑ r ∈ Finset.range n, (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ))
        = framePotential F N - (1 / 2 : ℝ) ^ n * framePotential F (N + n) := by
    intro n
    have h := framePotential_eq_partial F hF N n
    linarith
  have hzero : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * framePotential F (N + n))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero
      (fun n => mul_nonneg (by positivity) (framePotential_nonneg F (N + n)))
      (fun n => mul_le_mul_of_nonneg_left (framePotential_le_card F (N + n))
        (by positivity)) ?_
    have hp : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using hp.mul_const ((F.card : ℝ))
  have htend : Filter.Tendsto
      (fun n => ∑ r ∈ Finset.range n,
        (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ))
      Filter.atTop (nhds (framePotential F N)) := by
    simp only [heq]
    simpa using hzero.const_sub (framePotential F N)
  exact ((hasSum_iff_tendsto_nat_of_nonneg hnn _).mpr htend).tsum_eq.symm

/-! ### The geometric budget -/

theorem geometricPartial_eq (n : ℕ) :
    (∑ r ∈ Finset.range n, ((2 / 3 : ℝ) ^ (r + 1) - (1 / 2 : ℝ) ^ (r + 1)))
      = 1 - 2 * (2 / 3 : ℝ) ^ n + (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- The paper's `∑_{r ≥ 1} 2^{-r}((4/3)^r - 1) = 1`, in its finite form. -/
theorem geometricPartial_le_one (n : ℕ) :
    (∑ r ∈ Finset.range n, ((2 / 3 : ℝ) ^ (r + 1) - (1 / 2 : ℝ) ^ (r + 1))) ≤ 1 := by
  rw [geometricPartial_eq]
  have h1 : (1 / 2 : ℝ) ^ n ≤ (2 / 3 : ℝ) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h2 : (0 : ℝ) ≤ (2 / 3 : ℝ) ^ n := by positivity
  linarith

/-- If every shifted incidence obeys the geometric budget then `U_F(N) ≤ t`. -/
theorem framePotential_le_of_incidence_bound (F : Finset ℕ) (hF : 0 ∉ F)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hb : ∀ r : ℕ, 1 ≤ r →
      (incidenceCount F (N + r) : ℝ) ≤ t * ((4 / 3 : ℝ) ^ r - 1)) :
    framePotential F N ≤ t := by
  by_contra hcon
  push_neg at hcon
  have hcard : (0 : ℝ) < (F.card : ℝ) + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < (framePotential F N - t) / ((F.card : ℝ) + 1) by
      apply div_pos _ hcard
      linarith)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  rw [lt_div_iff₀ hcard] at hn
  have hsum : (∑ r ∈ Finset.range n,
      (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ)) ≤ t := by
    have hle : ∀ r ∈ Finset.range n,
        (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ)
          ≤ t * ((2 / 3 : ℝ) ^ (r + 1) - (1 / 2 : ℝ) ^ (r + 1)) := by
      intro r _
      have h := hb (r + 1) (by omega)
      have hidx : N + (r + 1) = N + r + 1 := by omega
      rw [hidx] at h
      have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (r + 1) := by positivity
      have hmul : (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ)
          ≤ (1 / 2 : ℝ) ^ (r + 1) * (t * ((4 / 3 : ℝ) ^ (r + 1) - 1)) :=
        mul_le_mul_of_nonneg_left h hpow
      have hbase : (1 / 2 : ℝ) ^ (r + 1) * (4 / 3 : ℝ) ^ (r + 1)
          = (2 / 3 : ℝ) ^ (r + 1) := by
        rw [← mul_pow]; norm_num
      have hid : (1 / 2 : ℝ) ^ (r + 1) * (t * ((4 / 3 : ℝ) ^ (r + 1) - 1))
          = t * ((2 / 3 : ℝ) ^ (r + 1) - (1 / 2 : ℝ) ^ (r + 1)) := by
        rw [← hbase]; ring
      linarith
    calc (∑ r ∈ Finset.range n,
        (1 / 2 : ℝ) ^ (r + 1) * (incidenceCount F (N + r + 1) : ℝ))
        ≤ ∑ r ∈ Finset.range n,
            t * ((2 / 3 : ℝ) ^ (r + 1) - (1 / 2 : ℝ) ^ (r + 1)) :=
          Finset.sum_le_sum hle
      _ = t * (∑ r ∈ Finset.range n,
            ((2 / 3 : ℝ) ^ (r + 1) - (1 / 2 : ℝ) ^ (r + 1))) := by
          rw [Finset.mul_sum]
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left (geometricPartial_le_one n) ht
      _ = t := mul_one t
  have hpart := framePotential_eq_partial F hF N n
  have htail : (1 / 2 : ℝ) ^ n * framePotential F (N + n)
      ≤ (1 / 2 : ℝ) ^ n * ((F.card : ℝ) + 1) := by
    have h1 : framePotential F (N + n) ≤ (F.card : ℝ) + 1 := by
      linarith [framePotential_le_card F (N + n)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/-- Paper step: `U_F(N) > t` forces a shifted incidence above the budget. -/
theorem exists_offset_of_framePotential_gt (F : Finset ℕ) (hF : 0 ∉ F)
    (N : ℕ) (t : ℝ) (ht : 0 < t) (hgt : t < framePotential F N) :
    ∃ r : ℕ, 1 ≤ r ∧
      (r : ℝ) * Real.log (4 / 3 : ℝ)
        < Real.log (1 + (incidenceCount F (N + r) : ℝ) / t) := by
  by_contra hcon
  push_neg at hcon
  have hb : ∀ r : ℕ, 1 ≤ r →
      (incidenceCount F (N + r) : ℝ) ≤ t * ((4 / 3 : ℝ) ^ r - 1) := by
    intro r hr
    have h := hcon r hr
    have hlogpow : Real.log ((4 / 3 : ℝ) ^ r) = (r : ℝ) * Real.log (4 / 3 : ℝ) := by
      rw [Real.log_pow]
    rw [← hlogpow] at h
    have hdiv : (0 : ℝ) ≤ (incidenceCount F (N + r) : ℝ) / t :=
      div_nonneg (Nat.cast_nonneg _) ht.le
    have hx : (0 : ℝ) < 1 + (incidenceCount F (N + r) : ℝ) / t := by linarith
    have hy : (0 : ℝ) < (4 / 3 : ℝ) ^ r := by positivity
    have hle : 1 + (incidenceCount F (N + r) : ℝ) / t ≤ (4 / 3 : ℝ) ^ r :=
      (Real.log_le_log_iff hx hy).mp h
    have hq : (incidenceCount F (N + r) : ℝ) / t ≤ (4 / 3 : ℝ) ^ r - 1 := by linarith
    calc (incidenceCount F (N + r) : ℝ)
        = (incidenceCount F (N + r) : ℝ) / t * t := by field_simp
      _ ≤ ((4 / 3 : ℝ) ^ r - 1) * t := mul_le_mul_of_nonneg_right hq ht.le
      _ = t * ((4 / 3 : ℝ) ^ r - 1) := by ring
  exact absurd (framePotential_le_of_incidence_bound F hF N t ht.le hb) (not_le.mpr hgt)

/-- The paper's "the constraints also hold at every positive integer `n`, by
replacing `n` with `gcd(n, Q)`". -/
theorem log_incidence_le_divisorMajorant {F : Finset ℕ} (hF : 0 ∉ F) {t : ℝ}
    {c : ℕ → ℝ}
    (hcon : ∀ s ∈ (frameLcm F).divisors,
      Real.log (1 + (incidenceCount F s : ℝ) / t) ≤ ∑ d ∈ s.divisors, c d)
    {n : ℕ} (hn : 0 < n) :
    Real.log (1 + (incidenceCount F n : ℝ) / t)
      ≤ divisorMajorant (frameLcm F).divisors c n := by
  classical
  have hQ0 : frameLcm F ≠ 0 := frameLcm_ne_zero hF
  have hs0 : Nat.gcd n (frameLcm F) ≠ 0 := fun h =>
    hQ0 (Nat.eq_zero_of_gcd_eq_zero_right h)
  have hsmem : Nat.gcd n (frameLcm F) ∈ (frameLcm F).divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n (frameLcm F), hQ0⟩
  have hfil : F.filter (fun a => a ∣ n)
      = F.filter (fun a => a ∣ Nat.gcd n (frameLcm F)) := by
    refine Finset.filter_congr ?_
    intro a ha
    exact ⟨fun h => Nat.dvd_gcd h (dvd_frameLcm ha),
      fun h => h.trans (Nat.gcd_dvd_left n (frameLcm F))⟩
  have hinc : incidenceCount F n = incidenceCount F (Nat.gcd n (frameLcm F)) := by
    unfold incidenceCount
    rw [hfil]
  have hdiv : (Nat.gcd n (frameLcm F)).divisors
      = (frameLcm F).divisors.filter (fun d => d ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right n (frameLcm F)), hQ0⟩,
        hd.trans (Nat.gcd_dvd_left n (frameLcm F))⟩
    · rintro ⟨⟨hdQ, -⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdQ, hs0⟩
  have h := hcon _ hsmem
  rw [← hinc, hdiv] at h
  exact h

/-! ### The counting bound -/

/-- The paper's counting estimate against one positive divisor majorant. -/
theorem count_mul_log_le_of_majorant (F : Finset ℕ) (hF : 0 ∉ F)
    (X : ℕ) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < t)
    (D : Finset ℕ) (c : ℕ → ℝ) (hc0 : ∀ d, 0 ≤ c d) (hDpos : ∀ d ∈ D, 0 < d)
    (hmaj : ∀ n : ℕ, 0 < n →
      Real.log (1 + (incidenceCount F n : ℝ) / t) ≤ divisorMajorant D c n) :
    ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ))
        * Real.log (4 / 3 : ℝ)
      ≤ 2 * divisorMajorantCost D c * (X : ℝ) := by
  classical
  have hapos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hKc0 : 0 ≤ divisorMajorantCost D c := divisorMajorantCost_nonneg hc0
  have hXR : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hWcard : ((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card ≤ X := by
    have hIcc : (Finset.Icc 1 X).card = X := by rw [Nat.card_Icc]; omega
    have h := Finset.card_filter_le (Finset.Icc 1 X) (fun N => t < framePotential F N)
    rw [hIcc] at h
    exact h
  have hWR : ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℕ) : ℝ)
      ≤ (X : ℝ) := by exact_mod_cast hWcard
  by_cases hcase : Real.log (4 / 3 : ℝ) ≤ 2 * divisorMajorantCost D c
  · have h1 := mul_le_mul_of_nonneg_right hWR hapos.le
    have h2 := mul_le_mul_of_nonneg_left hcase hXR
    nlinarith [h1, h2]
  · push_neg at hcase
    have hwit : ∀ N ∈ (Finset.Icc 1 X).filter (fun N => t < framePotential F N),
        ∃ n : ℕ, N < n ∧ n ≤ 2 * X ∧
          Real.log (4 / 3 : ℝ) * ((n : ℝ) - (N : ℝ)) < divisorMajorant D c n := by
      intro N hN
      have hNmem := Finset.mem_filter.mp hN
      have hNbounds := Finset.mem_Icc.mp hNmem.1
      obtain ⟨r, hr1, hr2⟩ :=
        exists_offset_of_framePotential_gt F hF N t ht hNmem.2
      have hnpos : 0 < N + r := by omega
      have hlog := hmaj (N + r) hnpos
      have hcast : (((N + r : ℕ)) : ℝ) - (N : ℝ) = (r : ℝ) := by push_cast; ring
      have hkey : Real.log (4 / 3 : ℝ) * (((N + r : ℕ) : ℝ) - (N : ℝ))
          < divisorMajorant D c (N + r) := by
        rw [hcast]
        calc Real.log (4 / 3 : ℝ) * (r : ℝ) = (r : ℝ) * Real.log (4 / 3 : ℝ) := by ring
          _ < Real.log (1 + (incidenceCount F (N + r) : ℝ) / t) := hr2
          _ ≤ divisorMajorant D c (N + r) := hlog
      refine ⟨N + r, by omega, ?_, hkey⟩
      have hgn := divisorMajorant_le_cost_mul hc0 hDpos hnpos
      have hstep : Real.log (4 / 3 : ℝ) * (((N + r : ℕ) : ℝ) - (N : ℝ))
          < divisorMajorantCost D c * ((N + r : ℕ) : ℝ) := lt_of_lt_of_le hkey hgn
      have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNbounds.1
      have hnR : (0 : ℝ) ≤ ((N + r : ℕ) : ℝ) := Nat.cast_nonneg _
      have hE2 : 0 ≤ ((N + r : ℕ) : ℝ) * (Real.log (4 / 3 : ℝ)
          - 2 * divisorMajorantCost D c) := mul_nonneg hnR (by linarith)
      have hhalf : Real.log (4 / 3 : ℝ) * ((N + r : ℕ) : ℝ)
          < Real.log (4 / 3 : ℝ) * (2 * (N : ℝ)) := by nlinarith [hE2, hstep]
      have hltn : N + r < 2 * N := by
        by_contra hbad
        push_neg at hbad
        have hcast : (2 : ℝ) * (N : ℝ) ≤ ((N + r : ℕ) : ℝ) := by exact_mod_cast hbad
        have hmul := mul_le_mul_of_nonneg_left hcast hapos.le
        linarith
      omega
    choose! Φ hΦlt hΦle hΦbound using hwit
    have hfiber : ((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card
        = ∑ n ∈ Finset.Icc 1 (2 * X),
            (((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).filter
              (fun N => Φ N = n)).card := by
      refine Finset.card_eq_sum_card_fiberwise ?_
      intro N hN
      have h1 := hΦlt N hN
      have h2 := hΦle N hN
      have hNbounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hN).1
      exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
    have hfib : ∀ n ∈ Finset.Icc 1 (2 * X),
        ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).filter
            (fun N => Φ N = n)).card : ℝ)
          ≤ divisorMajorant D c n / Real.log (4 / 3 : ℝ) := by
      intro n _
      have hgna : 0 ≤ divisorMajorant D c n / Real.log (4 / 3 : ℝ) :=
        div_nonneg (divisorMajorant_nonneg hc0 n) hapos.le
      have hcardle :
          ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).filter
              (fun N => Φ N = n)).card)
            ≤ (Finset.Icc 1
                (⌊divisorMajorant D c n / Real.log (4 / 3 : ℝ)⌋₊)).card := by
        refine Finset.card_le_card_of_injOn (fun N => n - N) ?_ ?_
        · intro N hN
          have hNmem := Finset.mem_filter.mp (Finset.mem_coe.mp hN)
          have h1 := hΦlt N hNmem.1
          have h3 := hΦbound N hNmem.1
          rw [hNmem.2] at h1 h3
          have hNn : N ≤ n := le_of_lt h1
          have hsub : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
            push_cast [Nat.cast_sub hNn]
            ring
          have hle : ((n - N : ℕ) : ℝ)
              ≤ divisorMajorant D c n / Real.log (4 / 3 : ℝ) := by
            rw [hsub, le_div_iff₀ hapos]
            linarith
          have hmem : n - N ∈ Finset.Icc 1
              (⌊divisorMajorant D c n / Real.log (4 / 3 : ℝ)⌋₊) :=
            Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hle⟩
          exact Finset.mem_coe.mpr hmem
        · intro N1 hN1 N2 hN2 heq
          have hM1 := Finset.mem_filter.mp (Finset.mem_coe.mp hN1)
          have hM2 := Finset.mem_filter.mp (Finset.mem_coe.mp hN2)
          have k1 := hΦlt N1 hM1.1
          have k2 := hΦlt N2 hM2.1
          rw [hM1.2] at k1
          rw [hM2.2] at k2
          simp only at heq
          omega
      have hIcc : (Finset.Icc 1
          (⌊divisorMajorant D c n / Real.log (4 / 3 : ℝ)⌋₊)).card
          = ⌊divisorMajorant D c n / Real.log (4 / 3 : ℝ)⌋₊ := by
        rw [Nat.card_Icc]; omega
      rw [hIcc] at hcardle
      calc ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).filter
              (fun N => Φ N = n)).card : ℝ)
          ≤ ((⌊divisorMajorant D c n / Real.log (4 / 3 : ℝ)⌋₊ : ℕ) : ℝ) := by
            exact_mod_cast hcardle
        _ ≤ divisorMajorant D c n / Real.log (4 / 3 : ℝ) := Nat.floor_le hgna
    have hWsum : ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℕ) : ℝ)
        ≤ (∑ n ∈ Finset.Icc 1 (2 * X), divisorMajorant D c n)
            / Real.log (4 / 3 : ℝ) := by
      rw [hfiber]
      push_cast
      rw [Finset.sum_div]
      exact Finset.sum_le_sum hfib
    have hmul : ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℕ) : ℝ)
        * Real.log (4 / 3 : ℝ)
        ≤ ∑ n ∈ Finset.Icc 1 (2 * X), divisorMajorant D c n :=
      (le_div_iff₀ hapos).mp hWsum
    have hY : 0 < 2 * X := by omega
    have hces := sum_divisorMajorant_le (D := D) hc0 hDpos hY
    have hcast : (((2 * X : ℕ)) : ℝ) = 2 * (X : ℝ) := by push_cast; ring
    rw [hcast] at hces
    linarith

/-- The counting estimate against one admissible logarithmic majorant. -/
theorem count_mul_log_le (F : Finset ℕ) (hF : 0 ∉ F)
    (X : ℕ) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < t)
    (c : ℕ → ℝ) (hc0 : ∀ d, 0 ≤ c d)
    (hcon : ∀ s ∈ (frameLcm F).divisors,
      Real.log (1 + (incidenceCount F s : ℝ) / t) ≤ ∑ d ∈ s.divisors, c d) :
    ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ))
        * Real.log (4 / 3 : ℝ)
      ≤ 2 * divisorMajorantCost (frameLcm F).divisors c * (X : ℝ) :=
  count_mul_log_le_of_majorant F hF X hX t ht ((frameLcm F).divisors) c hc0
    (fun d hd => Nat.pos_of_mem_divisors hd)
    (fun n hn => log_incidence_le_divisorMajorant hF hcon hn)

/-! ### The proposition -/

/-- Long `prop` "ordinary initial intervals"
(`paper/reasoning-parts/erdos257/a257_front.tex:9410`): for every finite
nonempty `F ⊆ ℕ_{>0}`, every integer `X ≥ 1` and every `0 < t ≤ 1`,

`#{1 ≤ N ≤ X : U_F(N) > t} / X ≤ (2 / log(4/3)) · κ₁(F;t)`. -/
theorem logarithmic_initial_interval (F : Finset ℕ) (hFne : F.Nonempty) (hF : 0 ∉ F)
    (X : ℕ) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ)) / (X : ℝ)
      ≤ 2 / Real.log (4 / 3 : ℝ) * kappaOne F t := by
  classical
  have hapos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hLne : Real.log (4 / 3 : ℝ) ≠ 0 := ne_of_gt hapos
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
  have hkey : Real.log (4 / 3 : ℝ) / 2 *
      (((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ)) / (X : ℝ))
        ≤ kappaOne F t := by
    refine le_csInf (logMajorantCosts_nonempty F ht) ?_
    rintro K ⟨c, hc0, hcon, rfl⟩
    have h := count_mul_log_le F hF X hX t ht c hc0 hcon
    rw [div_mul_div_comm,
      div_le_iff₀ (show (0 : ℝ) < 2 * (X : ℝ) by linarith)]
    nlinarith [h]
  have hcoef : (0 : ℝ) ≤ 2 / Real.log (4 / 3 : ℝ) :=
    le_of_lt (div_pos (by norm_num) hapos)
  have h2 := mul_le_mul_of_nonneg_left hkey hcoef
  have hid : (2 / Real.log (4 / 3 : ℝ)) *
      (Real.log (4 / 3 : ℝ) / 2 *
        (((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ))
          / (X : ℝ)))
      = ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ))
          / (X : ℝ) := by
    field_simp
  rw [hid] at h2
  exact h2

#print axioms framePotential_eq_tsum
#print axioms logMajorantCosts_nonempty
#print axioms count_mul_log_le
#print axioms logarithmic_initial_interval

end ErdosProblems.Erdos257.PaperCompleteR21

end
