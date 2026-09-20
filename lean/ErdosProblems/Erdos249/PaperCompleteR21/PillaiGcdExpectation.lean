import Erdos249257.GcdMomentCalculus

/-!
# The gcd-moment identity as an expectation (long #249 manuscript)

`prop:pillai` and `catalogue:mob:a5` of `paper/reasoning-parts/erdos249/a249_front.tex`
assert one three-member identity

  `∑_{d≥1} φ(d)/(2ᵈ-1)² = ∑_{n≥1} (P(n) - n)·2⁻ⁿ = E[gcd(X, Y)]`,

where `P(n) = ∑_{e ∣ n} φ(e)·(n/e) = (φ * Id)(n)` is Pillai's gcd-sum function
`P(n) = ∑_{k ≤ n} gcd(k, n)`, and `X, Y` are the independent fair-coin waiting
times of `prop:coprime`, `P(X = n) = P(Y = n) = 2⁻ⁿ` for `n ≥ 1`.

The first equality is the wave-19 Lambert rung
`GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series`.  What is
new here is the third member.  The law of `(X, Y)` puts mass `2^{-(a+b)}` on
each positive pair `(a, b)`, so the expectation the manuscript displays is the
explicit double series

  `E[gcd(X, Y)] = ∑_{a,b ≥ 1} gcd(a, b)·(1/2)^{a+b}`,

and `tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq` evaluates it as
`∑_{d≥1} φ(d)/(2ᵈ-1)²`.  The proof is a Tonelli interchange over
`ℕ × (ℕ × ℕ)` for the nonnegative family

  `F(d, (a,b)) = φ(d)·(1/2)^{a+b}·[d ≥ 1][d ∣ a][d ∣ b]`.

Summing in `d` first uses `∑_{d ∣ gcd(a,b)} φ(d) = gcd(a,b)` (`Nat.sum_totient`),
which is exactly the arithmetic reason the totient is the right weight; summing
in `(a,b)` first uses the pair-divisibility mass
`GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`, i.e.
`P(d ∣ X ∧ d ∣ Y) = 1/(2ᵈ-1)²`.  The interchange is licensed by
`summable_prod_of_nonneg`: every fibre in `(a,b)` is dominated by the geometric
pair series, and the resulting outer series `φ(d)/(2ᵈ-1)²` is dominated by
`4·2⁻ᵈ` because `φ(d) ≤ d < 2ᵈ` and `2ᵈ - 1 ≥ 2ᵈ⁻¹`.

Pillai's own identity `P(n) = ∑_{k=1}^{n} gcd(k, n)` and the convolution form
`P = φ * Id` are proved here too, so the manuscript's naming clause is carried
by theorems rather than by prose.

As everywhere in this corpus, no measure theory is used: the probability
reading is the documentation layer and every statement is an equality of
convergent real series.
-/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21

open GcdMomentCalculus
open scoped BigOperators

/-! ## Pillai's gcd-sum function -/

/-- Pillai's gcd-sum function, transcribed from the manuscript's defining
divisor sum `P(n) = ∑_{e ∣ n} φ(e)·(n/e)`. -/
def pillaiP (n : ℕ) : ℕ := ∑ e ∈ n.divisors, Nat.totient e * (n / e)

/-- `φ` as an `ArithmeticFunction` (`Nat.totient 0 = 0` already holds), so that
the manuscript's `φ * Id` is the Dirichlet convolution it names. -/
def totientArith : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

@[simp] lemma totientArith_apply (n : ℕ) : totientArith n = Nat.totient n := rfl

/-- **`P = φ * Id`** (`prop:pillai`, `catalogue:mob:a5`): the manuscript's
divisor sum is the Dirichlet convolution of `φ` with the identity function. -/
theorem pillaiP_eq_totient_mul_id (n : ℕ) :
    (totientArith * ArithmeticFunction.id) n = pillaiP n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => totientArith x * ArithmeticFunction.id y)]
  simp [pillaiP]

/-- **Pillai's gcd-sum identity** (`prop:pillai`, the clause naming `P`):
`∑_{k=1}^{n} gcd(k, n) = P(n)`.  Grouping `k` by the divisors of `n` that
divide it turns `gcd(k, n) = ∑_{d ∣ gcd(k,n)} φ(d)` into
`∑_{d ∣ n} φ(d)·#{k ≤ n : d ∣ k} = ∑_{d ∣ n} φ(d)·(n/d)`. -/
theorem sum_gcd_Icc_eq_pillaiP (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n = pillaiP n := by
  have hn0 : n ≠ 0 := hn.ne'
  have hfilter : ∀ k : ℕ,
      Finset.filter (fun d => d ∣ k) n.divisors = (Nat.gcd k n).divisors := by
    intro k
    have hgne : Nat.gcd k n ≠ 0 := by
      intro h
      have hdvd := Nat.gcd_dvd_right k n
      rw [h] at hdvd
      exact hn0 (zero_dvd_iff.mp hdvd)
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, -⟩, hdk⟩
      exact ⟨Nat.dvd_gcd hdk hdn, hgne⟩
    · rintro ⟨hdg, -⟩
      exact ⟨⟨hdg.trans (Nat.gcd_dvd_right k n), hn0⟩, hdg.trans (Nat.gcd_dvd_left k n)⟩
  have hstep : ∀ k ∈ Finset.Icc 1 n,
      Nat.gcd k n = ∑ d ∈ n.divisors, (if d ∣ k then Nat.totient d else 0) := by
    intro k _
    rw [← Finset.sum_filter, hfilter k]
    exact (Nat.sum_totient (Nat.gcd k n)).symm
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n
      = ∑ k ∈ Finset.Icc 1 n, ∑ d ∈ n.divisors, (if d ∣ k then Nat.totient d else 0) :=
        Finset.sum_congr rfl hstep
    _ = ∑ d ∈ n.divisors, ∑ k ∈ Finset.Icc 1 n, (if d ∣ k then Nat.totient d else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ n.divisors, Nat.totient d * (n / d) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hIcc, ← Finset.sum_filter, Finset.sum_const,
          Nat.Ioc_filter_dvd_card_eq_div, smul_eq_mul]
        exact Nat.mul_comm _ _
    _ = pillaiP n := rfl

private lemma pillaiP_cast (n : ℕ) :
    ((pillaiP n : ℕ) : ℝ) = ∑ e ∈ n.divisors, (Nat.totient e : ℝ) * (((n / e : ℕ)) : ℝ) := by
  rw [pillaiP, Nat.cast_sum]
  exact Finset.sum_congr rfl fun e _ => by push_cast; ring

/-! ## The totient-weighted squared-Mersenne series converges -/

/-- Absolute convergence of `∑_{d} φ(d)/(2ᵈ-1)²` over `ℕ`; at `d = 0` the term
is `0/0 = 0`, so the `ℕ`-indexed family agrees with the `ℕ+`-indexed one.
The bound is `φ(d) ≤ d < 2ᵈ` against `(2ᵈ-1)² ≥ 4ᵈ/4`. -/
theorem summable_totient_div_mersenne_sq_nat :
    Summable (fun d : ℕ => (Nat.totient d : ℝ) / ((2 : ℝ) ^ d - 1) ^ 2) := by
  have hgeo : Summable (fun d : ℕ => 4 * ((1 : ℝ) / 2) ^ d) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
  refine Summable.of_norm_bounded hgeo fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · norm_num
  · have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ d := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
        _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
    have hApos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    have hsq : (0 : ℝ) < ((2 : ℝ) ^ d - 1) ^ 2 := by nlinarith
    have hphi : (Nat.totient d : ℝ) ≤ (2 : ℝ) ^ d := by
      have h1 : Nat.totient d ≤ d := Nat.totient_le d
      have h2' : d < 2 ^ d := d.lt_two_pow_self
      have h3 : (Nat.totient d : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) := by
        exact_mod_cast le_of_lt (lt_of_le_of_lt h1 h2')
      simpa using h3
    have hphinn : (0 : ℝ) ≤ (Nat.totient d : ℝ) := by positivity
    have hgeq : 4 * ((1 : ℝ) / 2) ^ d = 4 / (2 : ℝ) ^ d := by
      rw [div_pow, one_pow]
      ring
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hphinn, abs_of_pos hsq, hgeq,
      div_le_div_iff₀ hsq hApos]
    nlinarith [mul_le_mul_of_nonneg_right hphi hApos.le,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * (2 : ℝ) ^ d - 2)
        (by linarith : (0 : ℝ) ≤ (2 : ℝ) ^ d - 2)]

private lemma tsum_nat_totient_div_mersenne_sq_eq_pnat :
    ∑' d : ℕ, (Nat.totient d : ℝ) / ((2 : ℝ) ^ d - 1) ^ 2
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  have h := tsum_zero_pnat_eq_tsum_nat
    (f := fun d : ℕ => (Nat.totient d : ℝ) / ((2 : ℝ) ^ d - 1) ^ 2)
    summable_totient_div_mersenne_sq_nat
  rw [← h]
  simp

/-! ## The Tonelli kernel `φ(d)·(1/2)^{a+b}·[d ∣ a][d ∣ b]` -/

/-- The nonnegative doubly indexed family whose two iterated sums are the two
sides of the gcd moment: in `(a,b)` it is the totient-weighted pair-divisibility
mass, in `d` it is `∑_{d ∣ gcd(a,b)} φ(d) = gcd(a,b)`. -/
private def gcdMomentKernel : ℕ × (ℕ × ℕ) → ℝ := fun q =>
  if 0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2 ∧ q.1 ∣ q.2.1 ∧ q.1 ∣ q.2.2
  then (Nat.totient q.1 : ℝ) * ((1 : ℝ) / 2) ^ (q.2.1 + q.2.2) else 0

private lemma gcdMomentKernel_apply (d : ℕ) (p : ℕ × ℕ) :
    gcdMomentKernel (d, p)
      = if 0 < d ∧ 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then (Nat.totient d : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0 := rfl

private lemma gcdMomentKernel_nonneg (q : ℕ × (ℕ × ℕ)) : 0 ≤ gcdMomentKernel q := by
  rw [show q = (q.1, q.2) from rfl, gcdMomentKernel_apply]
  split
  · positivity
  · exact le_rfl

private lemma summable_kernel_fiber_pairs (d : ℕ) :
    Summable (fun p : ℕ × ℕ => gcdMomentKernel (d, p)) := by
  have hmaj : Summable (fun p : ℕ × ℕ =>
      (Nat.totient d : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2)) :=
    (GeometricCoprimality.summable_pow_add (r := (1 : ℝ) / 2)
      (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun p => gcdMomentKernel_nonneg _) (fun p => ?_) hmaj
  rw [gcdMomentKernel_apply]
  split
  · exact le_rfl
  · positivity

private lemma tsum_kernel_fiber (d : ℕ) :
    ∑' p : ℕ × ℕ, gcdMomentKernel (d, p)
      = (Nat.totient d : ℝ) / ((2 : ℝ) ^ d - 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hpt : ∀ p : ℕ × ℕ, gcdMomentKernel (0, p) = 0 := by
      intro p
      rw [gcdMomentKernel_apply, if_neg]
      rintro ⟨h0, -⟩
      exact absurd h0 (lt_irrefl 0)
    rw [tsum_congr hpt, tsum_zero]
    norm_num
  · have hpt : ∀ p : ℕ × ℕ, gcdMomentKernel (d, p)
        = (Nat.totient d : ℝ)
          * (if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
              then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0) := by
      intro p
      rw [gcdMomentKernel_apply]
      by_cases h : 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
      · rw [if_pos ⟨hd, h.1, h.2.1, h.2.2.1, h.2.2.2⟩, if_pos h]
      · rw [if_neg (by tauto), if_neg h, mul_zero]
    rw [tsum_congr hpt, tsum_mul_left,
      tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq d hd, mul_one_div]

private lemma summable_kernel_fiber_nats (p : ℕ × ℕ) :
    Summable (fun d : ℕ => gcdMomentKernel (d, p)) := by
  refine summable_of_ne_finset_zero (s := Finset.range (Nat.gcd p.1 p.2 + 1)) ?_
  intro d hd
  rw [gcdMomentKernel_apply, if_neg]
  rintro ⟨-, ha, -, hda, hdb⟩
  have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 ha
  have hle := Nat.le_of_dvd hgpos (Nat.dvd_gcd hda hdb)
  rw [Finset.mem_range] at hd
  omega

/-- Summing the kernel in `d` recovers `gcd(a,b)·(1/2)^{a+b}`: the totient sum
over the divisors of `gcd(a,b)` is `gcd(a,b)`. -/
private lemma tsum_kernel_over_d (p : ℕ × ℕ) :
    ∑' d : ℕ, gcdMomentKernel (d, p)
      = if 0 < p.1 ∧ 0 < p.2
        then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0 := by
  by_cases hp : 0 < p.1 ∧ 0 < p.2
  · obtain ⟨ha, hb⟩ := hp
    rw [if_pos ⟨ha, hb⟩]
    have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 ha
    have hpt : ∀ d : ℕ, gcdMomentKernel (d, p)
        = (if 0 < d ∧ d ∣ p.1 ∧ d ∣ p.2 then (Nat.totient d : ℝ) else 0)
          * ((1 : ℝ) / 2) ^ (p.1 + p.2) := by
      intro d
      rw [gcdMomentKernel_apply]
      by_cases h : 0 < d ∧ d ∣ p.1 ∧ d ∣ p.2
      · rw [if_pos ⟨h.1, ha, hb, h.2.1, h.2.2⟩, if_pos h]
      · rw [if_neg (by tauto), if_neg h, zero_mul]
    rw [tsum_congr hpt, tsum_mul_right]
    congr 1
    have hzero : ∀ d ∉ Finset.range (Nat.gcd p.1 p.2 + 1),
        (if 0 < d ∧ d ∣ p.1 ∧ d ∣ p.2 then (Nat.totient d : ℝ) else 0) = 0 := by
      intro d hd
      rw [if_neg]
      rintro ⟨-, hda, hdb⟩
      have hle := Nat.le_of_dvd hgpos (Nat.dvd_gcd hda hdb)
      rw [Finset.mem_range] at hd
      omega
    have hsub : (Nat.gcd p.1 p.2).divisors ⊆ Finset.range (Nat.gcd p.1 p.2 + 1) := by
      intro d hd
      rw [Nat.mem_divisors] at hd
      rw [Finset.mem_range]
      have hle := Nat.le_of_dvd hgpos hd.1
      omega
    have hout : ∀ d ∈ Finset.range (Nat.gcd p.1 p.2 + 1),
        d ∉ (Nat.gcd p.1 p.2).divisors →
        (if 0 < d ∧ d ∣ p.1 ∧ d ∣ p.2 then (Nat.totient d : ℝ) else 0) = 0 := by
      intro d _ hd
      rw [if_neg]
      rintro ⟨-, hda, hdb⟩
      exact hd (Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hda hdb, hgpos.ne'⟩)
    have hin : ∀ d ∈ (Nat.gcd p.1 p.2).divisors,
        (if 0 < d ∧ d ∣ p.1 ∧ d ∣ p.2 then (Nat.totient d : ℝ) else 0)
          = (Nat.totient d : ℝ) := by
      intro d hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      rw [Nat.mem_divisors] at hd
      exact if_pos ⟨hd0, hd.1.trans (Nat.gcd_dvd_left p.1 p.2),
        hd.1.trans (Nat.gcd_dvd_right p.1 p.2)⟩
    rw [tsum_eq_sum hzero, ← Finset.sum_subset hsub hout, Finset.sum_congr rfl hin]
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) (Nat.sum_totient (Nat.gcd p.1 p.2))
  · rw [if_neg hp]
    have hpt : ∀ d : ℕ, gcdMomentKernel (d, p) = 0 := by
      intro d
      rw [gcdMomentKernel_apply, if_neg]
      rintro ⟨-, ha, hb, -, -⟩
      exact hp ⟨ha, hb⟩
    rw [tsum_congr hpt, tsum_zero]

private lemma summable_gcdMomentKernel : Summable gcdMomentKernel := by
  refine (summable_prod_of_nonneg (fun q => gcdMomentKernel_nonneg q)).mpr
    ⟨fun d => summable_kernel_fiber_pairs d, ?_⟩
  exact summable_totient_div_mersenne_sq_nat.congr fun d => (tsum_kernel_fiber d).symm

/-! ## The third member: the expected gcd -/

/-- **The expected gcd of two independent fair-coin waiting times**
(`prop:pillai`, third member; `catalogue:mob:a5`, second sentence).

`X` and `Y` are independent with `P(X = n) = P(Y = n) = 2⁻ⁿ` for `n ≥ 1`, so the
pair `(X, Y)` puts mass `(1/2)^{a+b}` on each positive pair `(a, b)` and the
expectation is the displayed double series

  `E[gcd(X, Y)] = ∑_{a,b ≥ 1} gcd(a, b)·(1/2)^{a+b} = ∑_{d≥1} φ(d)/(2ᵈ-1)²`.

This is the same explicit sum convention the corpus already uses for the pair
laws `tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq` and
`tsum_pos_coprime_inv_mersenne_eq_one`. -/
theorem tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
        then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  have hA : ∑' q : ℕ × (ℕ × ℕ), gcdMomentKernel q
      = ∑' d : ℕ, (Nat.totient d : ℝ) / ((2 : ℝ) ^ d - 1) ^ 2 := by
    rw [summable_gcdMomentKernel.tsum_prod' (fun d => summable_kernel_fiber_pairs d)]
    exact tsum_congr fun d => tsum_kernel_fiber d
  have hB : ∑' q : ℕ × (ℕ × ℕ), gcdMomentKernel q
      = ∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
          then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0 := by
    have hswap : Summable (fun q : (ℕ × ℕ) × ℕ => gcdMomentKernel q.swap) :=
      summable_gcdMomentKernel.prod_symm
    have h1 : ∑' q : ℕ × (ℕ × ℕ), gcdMomentKernel q
        = ∑' q : (ℕ × ℕ) × ℕ, gcdMomentKernel q.swap :=
      (Equiv.prodComm ℕ (ℕ × ℕ)).tsum_eq (fun q : (ℕ × ℕ) × ℕ => gcdMomentKernel q.swap)
    rw [h1, hswap.tsum_prod' (fun p => summable_kernel_fiber_nats p)]
    exact tsum_congr fun p => tsum_kernel_over_d p
  rw [← hB, hA, tsum_nat_totient_div_mersenne_sq_eq_pnat]

/-- **The gcd-moment identity** (`prop:pillai`; `catalogue:mob:a5`):
the full three-member display

  `∑_{d≥1} φ(d)/(2ᵈ-1)² = ∑_{n≥1} (P(n) - n)·(1/2)ⁿ = E[gcd(X, Y)]`,

with `P` Pillai's gcd-sum function `pillaiP` and `E[gcd(X, Y)]` the explicit
fair-coin double series. -/
theorem gcd_moment_identity_three_members :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' n : ℕ+, (((pillaiP (n : ℕ) : ℕ) : ℝ) - ((n : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ))
      ∧ (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
            then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0) := by
  refine ⟨?_, tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq.symm⟩
  rw [tsum_totient_div_mersenne_sq_eq_gcd_moment_series]
  refine tsum_congr fun n => ?_
  rw [pillaiP_cast]

#print axioms pillaiP_eq_totient_mul_id
#print axioms sum_gcd_Icc_eq_pillaiP
#print axioms summable_totient_div_mersenne_sq_nat
#print axioms tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq
#print axioms gcd_moment_identity_three_members
#print axioms GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series
#print axioms GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq
end ErdosProblems.Erdos249.PaperCompleteR21
