import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleSelection
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleTagFamily
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleChebyshev
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleCrtCounts
import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCoverLowerBoundPaperForm

/-!
# Assembly of the arithmetic logarithmic counterexample (long #257, line 9212)

The remaining steps of the long Erdős #257 `thm` "arithmetic logarithmic
counterexample" (`paper/reasoning-parts/erdos257/a257_front.tex:9212`), on top of
the layers already built:

* `ArithmeticCounterexampleSelection.lean` — the prime and divisor selections;
* `ArithmeticCounterexampleEncoding.lean` — `f_{F_q}(n) = 1_{q ∣ n} 2^{Z_q(n)}`,
  the logarithmic majorant and its cost, and the summing step
  `kappaOne_biUnion_frame_le`;
* `ArithmeticCounterexampleTagFamily.lean` — one parent group built from the
  selected tag sets;
* `ArithmeticCounterexampleChebyshev.lean` — second moment, Chebyshev as a
  count, and `∏(1 - x_q) ≤ exp(-∑ x_q)`;
* `ArithmeticCounterexampleCrtCounts.lean` — the exact count
  `#{m < M : ∀ i ∈ S, n_i ∣ L m + c_i} = M / ∏ n_i`.

This module supplies, in order:

1. the Chinese remainder theorem as a **product of independent residue
   conditions** (`card_filter_forall_mod_mem`), which is the paper's "different
   parent groups depend on disjoint prime coordinates, so the `E_q` are
   independent";
2. the per-parent conditional Chebyshev estimate
   ("success has conditional probability at least `1/2`") and the union over
   `r ∈ G` ("the event `E_q` of success for some `r ∈ G` satisfies
   `ℙ_L(E_q) ≥ |G|/(2q) ≥ D/(4q)`");
3. the construction of the whole family and the endpoints stating every clause
   of the theorem and of the corollary `cor:257-logarithmic-separation`.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset
open ErdosProblems.Erdos257.PaperCompleteR8

/-! ### Products of pairwise coprime divisors -/

/-- Pairwise coprime divisors of `M` have a product dividing `M`. -/
theorem prod_dvd_of_pairwise_coprime {ι : Type*} [DecidableEq ι] {M : ℕ} (S : Finset ι)
    (f : ι → ℕ)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (f i) (f j))
    (hdvd : ∀ i ∈ S, f i ∣ M) : (∏ i ∈ S, f i) ∣ M := by
  classical
  revert hcop hdvd
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a T ha ih =>
      intro hcop hdvd
      have hcopT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Nat.Coprime (f i) (f j) := fun i hi j hj hij =>
        hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hprodT : (∏ i ∈ T, f i) ∣ M :=
        ih hcopT (fun i hi => hdvd i (Finset.mem_insert_of_mem hi))
      have hca : Nat.Coprime (f a) (∏ i ∈ T, f i) :=
        Nat.Coprime.prod_right fun i hi =>
          hcop a (Finset.mem_insert_self a T) i (Finset.mem_insert_of_mem hi)
            (fun h => ha (by rw [h]; exact hi))
      rw [Finset.prod_insert ha]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hca
        (hdvd a (Finset.mem_insert_self a T)) hprodT

/-! ### The Chinese remainder theorem as a product of residue conditions -/

/-- Two coprime residue conditions are jointly free over one full period. -/
theorem card_filter_mod_mem_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (A B : Finset ℕ) :
    ((Finset.range (a * b)).filter (fun m => m % a ∈ A ∧ m % b ∈ B)).card
      = ((Finset.range a).filter (fun x => x ∈ A)).card
        * ((Finset.range b).filter (fun y => y ∈ B)).card := by
  classical
  have hab0 : 0 < a * b := Nat.mul_pos ha hb
  rw [← Finset.card_product]
  refine Finset.card_bij (fun m _ => (m % a, m % b)) ?_ ?_ ?_
  · intro m hm
    have h := Finset.mem_filter.mp hm
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ ha), h.2.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hb), h.2.2⟩
  · intro m1 h1 m2 h2 heq
    have e1 : m1 % a = m2 % a := congrArg Prod.fst heq
    have e2 : m1 % b = m2 % b := congrArg Prod.snd heq
    have hm1 : m1 < a * b := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    have hm2 : m2 < a * b := Finset.mem_range.mp (Finset.mem_filter.mp h2).1
    have hmod : m1 % (a * b) = m2 % (a * b) :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨e1, e2⟩
    rwa [Nat.mod_eq_of_lt hm1, Nat.mod_eq_of_lt hm2] at hmod
  · rintro ⟨x, z⟩ hxz
    obtain ⟨hx, hz⟩ := Finset.mem_product.mp hxz
    obtain ⟨hxr, hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨hzr, hzB⟩ := Finset.mem_filter.mp hz
    have hxlt : x < a := Finset.mem_range.mp hxr
    have hzlt : z < b := Finset.mem_range.mp hzr
    obtain ⟨k, hka, hkb⟩ := Nat.chineseRemainder hab x z
    have hdvda : a ∣ a * b := ⟨b, rfl⟩
    have hdvdb : b ∣ a * b := ⟨a, mul_comm a b⟩
    have hma : k % (a * b) % a = x := by
      rw [Nat.mod_mod_of_dvd k hdvda]
      have h : k % a = x % a := hka
      rw [h, Nat.mod_eq_of_lt hxlt]
    have hmb : k % (a * b) % b = z := by
      rw [Nat.mod_mod_of_dvd k hdvdb]
      have h : k % b = z % b := hkb
      rw [h, Nat.mod_eq_of_lt hzlt]
    refine ⟨k % (a * b), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hab0), ?_, ?_⟩
      · rw [hma]; exact hxA
      · rw [hmb]; exact hzB
    · simp only [hma, hmb]

/-- Over one full period `∏_{i ∈ S} K_i`, residue conditions at pairwise coprime
moduli are jointly free. -/
theorem card_filter_forall_mod_mem_prod {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (K : ι → ℕ) (Rs : ι → Finset ℕ)
    (hK : ∀ i ∈ S, 0 < K i)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (K i) (K j)) :
    ((Finset.range (∏ i ∈ S, K i)).filter (fun m => ∀ i ∈ S, m % K i ∈ Rs i)).card
      = ∏ i ∈ S, ((Finset.range (K i)).filter (fun x => x ∈ Rs i)).card := by
  classical
  revert hK hcop
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a T ha ih =>
      intro hK hcop
      have hKT : ∀ i ∈ T, 0 < K i := fun i hi => hK i (Finset.mem_insert_of_mem hi)
      have hcopT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Nat.Coprime (K i) (K j) := fun i hi j hj hij =>
        hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hKa : 0 < K a := hK a (Finset.mem_insert_self a T)
      have hV : 0 < ∏ i ∈ T, K i := Finset.prod_pos hKT
      have hcopaV : Nat.Coprime (K a) (∏ i ∈ T, K i) :=
        Nat.Coprime.prod_right fun i hi =>
          hcop a (Finset.mem_insert_self a T) i (Finset.mem_insert_of_mem hi)
            (fun h => ha (by rw [h]; exact hi))
      have hKdvdV : ∀ i ∈ T, K i ∣ ∏ j ∈ T, K j := fun i hi => Finset.dvd_prod_of_mem K hi
      have hiff : ∀ m : ℕ, (∀ i ∈ T, m % K i ∈ Rs i)
          ↔ m % (∏ j ∈ T, K j) ∈ (Finset.range (∏ j ∈ T, K j)).filter
              (fun y => ∀ i ∈ T, y % K i ∈ Rs i) := by
        intro m
        constructor
        · intro h
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hV), ?_⟩
          intro i hi
          rw [Nat.mod_mod_of_dvd m (hKdvdV i hi)]
          exact h i hi
        · intro h i hi
          have h2 := (Finset.mem_filter.mp h).2 i hi
          rwa [Nat.mod_mod_of_dvd m (hKdvdV i hi)] at h2
      have hprodK : (∏ i ∈ insert a T, K i) = K a * ∏ i ∈ T, K i := Finset.prod_insert ha
      have hprodC :
          (∏ i ∈ insert a T, ((Finset.range (K i)).filter (fun x => x ∈ Rs i)).card)
            = ((Finset.range (K a)).filter (fun x => x ∈ Rs a)).card
              * ∏ i ∈ T, ((Finset.range (K i)).filter (fun x => x ∈ Rs i)).card :=
        Finset.prod_insert ha
      have hset : (Finset.range (K a * ∏ i ∈ T, K i)).filter
            (fun m => ∀ i ∈ insert a T, m % K i ∈ Rs i)
          = (Finset.range (K a * ∏ i ∈ T, K i)).filter
            (fun m => m % K a ∈ Rs a ∧ m % (∏ j ∈ T, K j) ∈
              (Finset.range (∏ j ∈ T, K j)).filter
                (fun y => ∀ i ∈ T, y % K i ∈ Rs i)) := by
        refine Finset.filter_congr ?_
        intro m _
        rw [Finset.forall_mem_insert, hiff m]
      have hBsub : (Finset.range (∏ j ∈ T, K j)).filter (fun y => ∀ i ∈ T, y % K i ∈ Rs i)
          ⊆ Finset.range (∏ j ∈ T, K j) := Finset.filter_subset _ _
      have hBfil : (Finset.range (∏ j ∈ T, K j)).filter
            (fun y => y ∈ (Finset.range (∏ j ∈ T, K j)).filter
              (fun y => ∀ i ∈ T, y % K i ∈ Rs i))
          = (Finset.range (∏ j ∈ T, K j)).filter (fun y => ∀ i ∈ T, y % K i ∈ Rs i) := by
        rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hBsub]
      rw [hprodK, hprodC, hset, card_filter_mod_mem_mul hKa hV hcopaV (Rs a) _, hBfil]
      congr 1
      exact ih hKT hcopT

/-- The paper's independence of the parent groups, as an exact count: over any
period divisible by `∏_{i ∈ S} K_i`, residue conditions at pairwise coprime
moduli multiply. -/
theorem card_filter_forall_mod_mem {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (K : ι → ℕ) (Rs : ι → Finset ℕ)
    (hK : ∀ i ∈ S, 0 < K i)
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (K i) (K j))
    {M : ℕ} (hdvd : (∏ i ∈ S, K i) ∣ M) :
    ((Finset.range M).filter (fun m => ∀ i ∈ S, m % K i ∈ Rs i)).card * (∏ i ∈ S, K i)
      = M * ∏ i ∈ S, ((Finset.range (K i)).filter (fun x => x ∈ Rs i)).card := by
  classical
  have hW : 0 < ∏ i ∈ S, K i := Finset.prod_pos hK
  have hKdvdW : ∀ i ∈ S, K i ∣ ∏ j ∈ S, K j := fun i hi => Finset.dvd_prod_of_mem K hi
  have hiff : ∀ m : ℕ, (∀ i ∈ S, m % K i ∈ Rs i)
      ↔ m % (∏ j ∈ S, K j) ∈ (Finset.range (∏ j ∈ S, K j)).filter
          (fun y => ∀ i ∈ S, y % K i ∈ Rs i) := by
    intro m
    constructor
    · intro h
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hW), ?_⟩
      intro i hi
      rw [Nat.mod_mod_of_dvd m (hKdvdW i hi)]
      exact h i hi
    · intro h i hi
      have h2 := (Finset.mem_filter.mp h).2 i hi
      rwa [Nat.mod_mod_of_dvd m (hKdvdW i hi)] at h2
  have hset : (Finset.range M).filter (fun m => ∀ i ∈ S, m % K i ∈ Rs i)
      = (Finset.range M).filter (fun m => m % (∏ j ∈ S, K j) ∈
          (Finset.range (∏ j ∈ S, K j)).filter (fun y => ∀ i ∈ S, y % K i ∈ Rs i)) :=
    Finset.filter_congr (fun m _ => hiff m)
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := fun m => m % (∏ j ∈ S, K j))
    (s := (Finset.range M).filter (fun m => m % (∏ j ∈ S, K j) ∈
          (Finset.range (∏ j ∈ S, K j)).filter (fun y => ∀ i ∈ S, y % K i ∈ Rs i)))
    (t := (Finset.range (∏ j ∈ S, K j)).filter (fun y => ∀ i ∈ S, y % K i ∈ Rs i))
    (fun m hm => (Finset.mem_filter.mp hm).2)
  have hfib : ∀ x ∈ (Finset.range (∏ j ∈ S, K j)).filter
        (fun y => ∀ i ∈ S, y % K i ∈ Rs i),
      (((Finset.range M).filter (fun m => m % (∏ j ∈ S, K j) ∈
          (Finset.range (∏ j ∈ S, K j)).filter
            (fun y => ∀ i ∈ S, y % K i ∈ Rs i))).filter
        (fun m => m % (∏ j ∈ S, K j) = x)).card = M / ∏ j ∈ S, K j := by
    intro x hx
    have hxlt : x < ∏ j ∈ S, K j := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hx2 : ∀ i ∈ S, x % K i ∈ Rs i := (Finset.mem_filter.mp hx).2
    have hrepl : ((Finset.range M).filter (fun m => m % (∏ j ∈ S, K j) ∈
          (Finset.range (∏ j ∈ S, K j)).filter
            (fun y => ∀ i ∈ S, y % K i ∈ Rs i))).filter
        (fun m => m % (∏ j ∈ S, K j) = x)
        = (Finset.range M).filter (fun m => m % (∏ j ∈ S, K j) = x) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by rw [h3]; exact ⟨hxlt, hx2⟩⟩, h3⟩
    rw [hrepl, crtCard_filter_mod_eq hW hxlt hdvd]
  have hcard : ((Finset.range M).filter (fun m => ∀ i ∈ S, m % K i ∈ Rs i)).card
      = ((Finset.range (∏ j ∈ S, K j)).filter
          (fun y => ∀ i ∈ S, y % K i ∈ Rs i)).card * (M / ∏ j ∈ S, K j) := by
    rw [hset, hfiber, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  rw [hcard, mul_assoc, Nat.div_mul_cancel hdvd,
    card_filter_forall_mod_mem_prod S K Rs hK hcop]
  exact Nat.mul_comm _ _

/-! ### Chebyshev's inequality in the paper's conditional form

"Conditional on one such event, the tag-prime events remain independent by the
Chinese remainder theorem ... the mean of `Z_q(N+r)` is `μ_r ≥ 4r` and its
variance is at most `μ_r`.  Chebyshev's inequality gives
`ℙ(Z_q(N+r) < r ∣ q ∣ N+r) ≤ μ_r/(μ_r - r)² ≤ 4/(9r) ≤ 4/9.  Thus success has
conditional probability at least `1/2`." -/

/-- The paper's conditional Chebyshev step, over an arbitrary finite sample set:
if the events `A p`, `p ∈ Sg`, have frequencies `1/p` and pairwise frequencies
`(1/p)(1/p')`, and their expected number `∑ 1/p` is at least `4r`, then at least
half the sample points carry at least `r` of them. -/
theorem half_card_le_card_filter_le {α : Type*} [DecidableEq α] (Ω : Finset α)
    (Sg : Finset ℕ) (Av : ℕ → Finset α) (r : ℕ) (hrpos : 0 < r)
    (hA : ∀ p ∈ Sg, Av p ⊆ Ω)
    (hmarg : ∀ p ∈ Sg, ((Av p).card : ℝ) = (Ω.card : ℝ) * (1 / (p : ℝ)))
    (hpair : ∀ p ∈ Sg, ∀ p' ∈ Sg, p ≠ p' →
      ((Av p ∩ Av p').card : ℝ) = (Ω.card : ℝ) * ((1 / (p : ℝ)) * (1 / (p' : ℝ))))
    (hmu : 4 * (r : ℝ) ≤ ∑ p ∈ Sg, 1 / (p : ℝ)) :
    (Ω.card : ℝ) / 2
      ≤ (((Ω.filter (fun k => r ≤ (Sg.filter (fun p => k ∈ Av p)).card)).card : ℕ) : ℝ) := by
  classical
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
  have hrmu : (r : ℝ) < ∑ p ∈ Sg, 1 / (p : ℝ) := by linarith
  have hcheb := sum_sq_sub_mean_le Ω Sg Av (fun p => 1 / (p : ℝ)) hA hmarg hpair
  have hlt := card_lt_le_of_sum_sq Ω
    (fun k => ∑ p ∈ Sg, (if k ∈ Av p then (1 : ℝ) else 0))
    (∑ p ∈ Sg, 1 / (p : ℝ)) (∑ p ∈ Sg, 1 / (p : ℝ)) (r : ℝ) hrmu hcheb
  have hXc : ∀ k : α, (∑ p ∈ Sg, (if k ∈ Av p then (1 : ℝ) else 0))
      = (((Sg.filter (fun p => k ∈ Av p)).card : ℕ) : ℝ) := by
    intro k
    rw [Finset.sum_boole]
  have hfe : Ω.filter (fun k => (∑ p ∈ Sg, (if k ∈ Av p then (1 : ℝ) else 0)) < (r : ℝ))
      = Ω.filter (fun k => ¬ (r ≤ (Sg.filter (fun p => k ∈ Av p)).card)) := by
    refine Finset.filter_congr ?_
    intro k _
    rw [hXc k]
    constructor
    · intro h hle
      have h2 : ((r : ℕ) : ℝ) ≤ (((Sg.filter (fun p => k ∈ Av p)).card : ℕ) : ℝ) := by
        exact_mod_cast hle
      linarith
    · intro h
      have h2 : (Sg.filter (fun p => k ∈ Av p)).card < r := by omega
      exact_mod_cast h2
  rw [hfe] at hlt
  have hd : (0 : ℝ) < ((∑ p ∈ Sg, 1 / (p : ℝ)) - (r : ℝ)) ^ 2 := by
    have hpos : (0 : ℝ) < (∑ p ∈ Sg, 1 / (p : ℝ)) - (r : ℝ) := by linarith
    positivity
  have hkey : 9 * (r : ℝ) * (∑ p ∈ Sg, 1 / (p : ℝ))
      ≤ 4 * ((∑ p ∈ Sg, 1 / (p : ℝ)) - (r : ℝ)) ^ 2 := by
    have h9 : (0 : ℝ) < 9 * (r : ℝ) := by linarith
    have hm := mean_div_sq_le hr0 hmu
    rw [div_le_div_iff₀ hd h9] at hm
    linarith
  have hn0 : (0 : ℝ) ≤ (Ω.card : ℝ) := Nat.cast_nonneg _
  have hA0 : (0 : ℝ)
      ≤ (((Ω.filter (fun k => ¬ (r ≤ (Sg.filter (fun p => k ∈ Av p)).card))).card : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hstep : (((Ω.filter (fun k => ¬ (r ≤ (Sg.filter (fun p => k ∈ Av p)).card))).card : ℕ) : ℝ)
        * ((∑ p ∈ Sg, 1 / (p : ℝ)) - (r : ℝ)) ^ 2 * (9 * (r : ℝ))
      ≤ 4 * ((Ω.card : ℝ) * ((∑ p ∈ Sg, 1 / (p : ℝ)) - (r : ℝ)) ^ 2) := by
    calc (((Ω.filter (fun k => ¬ (r ≤ (Sg.filter (fun p => k ∈ Av p)).card))).card : ℕ) : ℝ)
            * ((∑ p ∈ Sg, 1 / (p : ℝ)) - (r : ℝ)) ^ 2 * (9 * (r : ℝ))
        ≤ ((Ω.card : ℝ) * (∑ p ∈ Sg, 1 / (p : ℝ))) * (9 * (r : ℝ)) :=
          mul_le_mul_of_nonneg_right hlt (by linarith)
      _ = (Ω.card : ℝ) * (9 * (r : ℝ) * (∑ p ∈ Sg, 1 / (p : ℝ))) := by ring
      _ ≤ (Ω.card : ℝ) * (4 * ((∑ p ∈ Sg, 1 / (p : ℝ)) - (r : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey hn0
      _ = 4 * ((Ω.card : ℝ) * ((∑ p ∈ Sg, 1 / (p : ℝ)) - (r : ℝ)) ^ 2) := by ring
  have h9r : (((Ω.filter (fun k => ¬ (r ≤ (Sg.filter (fun p => k ∈ Av p)).card))).card : ℕ) : ℝ)
      * (9 * (r : ℝ)) ≤ 4 * (Ω.card : ℝ) := by
    nlinarith [hstep, hd]
  have hquarter :
      (((Ω.filter (fun k => ¬ (r ≤ (Sg.filter (fun p => k ∈ Av p)).card))).card : ℕ) : ℝ)
        ≤ (Ω.card : ℝ) * (4 / 9) := by
    nlinarith [h9r, mul_nonneg hA0 (by linarith : (0 : ℝ) ≤ (r : ℝ) - 1)]
  have hsum : (Ω.filter (fun k => r ≤ (Sg.filter (fun p => k ∈ Av p)).card)).card
      + (Ω.filter (fun k => ¬ (r ≤ (Sg.filter (fun p => k ∈ Av p)).card))).card = Ω.card :=
    Finset.card_filter_add_card_filter_not (s := Ω) _
  have hsumR : (((Ω.filter (fun k => r ≤ (Sg.filter (fun p => k ∈ Av p)).card)).card : ℕ) : ℝ)
      + (((Ω.filter (fun k => ¬ (r ≤ (Sg.filter (fun p => k ∈ Av p)).card))).card : ℕ) : ℝ)
      = (Ω.card : ℝ) := by exact_mod_cast hsum
  linarith

namespace TagFamily

variable (T : TagFamily)

/-! ### One parent group: its own period and its conditional tag index -/

/-- The period of the sampling events of one parent group: the product of its
parent prime and of all its tag primes. -/
def period : ℕ := T.parent * primeProd T.tagIndex

/-- The labelled pairs of `𝓘_q` whose divisor part divides `r`.  Because
`d ∣ N + r` is equivalent to `d ∣ r` for `d ∣ L` and `L ∣ N`, these index exactly
the tag events that survive at offset `r`. -/
def condTags (r : ℕ) : Finset ℕ :=
  (T.L.divisors.filter (fun d => d ∣ r)).biUnion T.tags

theorem parent_notMem_tagIndex : T.parent ∉ T.tagIndex := by
  intro h
  obtain ⟨d, hd, hpd⟩ := T.mem_tagIndex_iff.mp h
  exact T.tag_ne_parent d hd T.parent hpd rfl

theorem not_dvd_L_of_mem_tagIndex {p : ℕ} (hp : p ∈ T.tagIndex) : ¬ p ∣ T.L := by
  obtain ⟨d, hd, hpd⟩ := T.mem_tagIndex_iff.mp hp
  exact T.tag_not_dvd_L d hd p hpd

theorem parent_not_dvd_L : ¬ T.parent ∣ T.L := by
  intro h
  have h1 := Nat.le_of_dvd T.L_pos h
  have h2 := T.L_lt_parent
  omega

theorem primeSet_prime {a : ℕ} (ha : a ∈ insert T.parent T.tagIndex) : a.Prime := by
  rcases Finset.mem_insert.mp ha with rfl | h
  · exact T.parent_prime
  · exact T.tagIndex_prime h

theorem primeSet_not_dvd_L {a : ℕ} (ha : a ∈ insert T.parent T.tagIndex) : ¬ a ∣ T.L := by
  rcases Finset.mem_insert.mp ha with rfl | h
  · exact T.parent_not_dvd_L
  · exact T.not_dvd_L_of_mem_tagIndex h

theorem primeSet_coprime_L {a : ℕ} (ha : a ∈ insert T.parent T.tagIndex) :
    Nat.Coprime a T.L :=
  (Nat.Prime.coprime_iff_not_dvd (T.primeSet_prime ha)).mpr (T.primeSet_not_dvd_L ha)

theorem period_pos : 0 < T.period :=
  Nat.mul_pos T.parent_prime.pos (primeProd_pos (fun p hp => T.tagIndex_prime hp))

theorem primeSet_dvd_period {a : ℕ} (ha : a ∈ insert T.parent T.tagIndex) :
    a ∣ T.period := by
  unfold period
  rcases Finset.mem_insert.mp ha with rfl | h
  · exact dvd_mul_right _ _
  · refine Dvd.dvd.mul_left ?_ T.parent
    unfold primeProd
    exact Finset.dvd_prod_of_mem (fun p => p) h

theorem prod_dvd_period {S : Finset ℕ} (hS : S ⊆ insert T.parent T.tagIndex) :
    (∏ a ∈ S, a) ∣ T.period :=
  Finset.prod_primes_dvd _ (fun a ha => (T.primeSet_prime (hS ha)).prime)
    (fun a ha => T.primeSet_dvd_period (hS ha))

/-- The paper's sampling count for one parent group: at any family of its own
primes the divisibility events `a ∣ L k + c` are jointly free over one period. -/
theorem crt_count {S : Finset ℕ} (hS : S ⊆ insert T.parent T.tagIndex) (c : ℕ) :
    ((((Finset.range T.period).filter
        (fun k => ∀ a ∈ S, a ∣ T.L * k + c)).card : ℕ) : ℝ)
      = (T.period : ℝ) * (1 / ((∏ a ∈ S, a : ℕ) : ℝ)) := by
  classical
  have h := crtFreq_dvd_linear_family (M := T.period) (L := T.L) S (fun a => a)
    (fun _ => c)
    (fun a ha => (T.primeSet_prime (hS ha)).pos)
    (fun a ha => T.primeSet_coprime_L (hS ha))
    (fun a ha b hb hab =>
      (Nat.coprime_primes (T.primeSet_prime (hS ha)) (T.primeSet_prime (hS hb))).mpr hab)
    (T.prod_dvd_period hS)
  rw [Finset.card_range] at h
  exact h

theorem crt_count_one {a : ℕ} (ha : a ∈ insert T.parent T.tagIndex) (c : ℕ) :
    ((((Finset.range T.period).filter (fun k => a ∣ T.L * k + c)).card : ℕ) : ℝ)
      = (T.period : ℝ) / (a : ℝ) := by
  classical
  have hsub : ({a} : Finset ℕ) ⊆ insert T.parent T.tagIndex := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    exact hx ▸ ha
  have hfil : (Finset.range T.period).filter
        (fun k => ∀ x ∈ ({a} : Finset ℕ), x ∣ T.L * k + c)
      = (Finset.range T.period).filter (fun k => a ∣ T.L * k + c) := by
    refine Finset.filter_congr ?_
    intro k _
    simp
  have h := T.crt_count hsub c
  rw [hfil, Finset.prod_singleton] at h
  rw [h]
  ring

theorem crt_count_two {a b : ℕ} (ha : a ∈ insert T.parent T.tagIndex)
    (hb : b ∈ insert T.parent T.tagIndex) (hab : a ≠ b) (c : ℕ) :
    ((((Finset.range T.period).filter
        (fun k => a ∣ T.L * k + c ∧ b ∣ T.L * k + c)).card : ℕ) : ℝ)
      = (T.period : ℝ) / ((a : ℝ) * (b : ℝ)) := by
  classical
  have hsub : ({a, b} : Finset ℕ) ⊆ insert T.parent T.tagIndex := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact ha
    · rw [Finset.mem_singleton] at hx'
      exact hx' ▸ hb
  have hfil : (Finset.range T.period).filter
        (fun k => ∀ x ∈ ({a, b} : Finset ℕ), x ∣ T.L * k + c)
      = (Finset.range T.period).filter
        (fun k => a ∣ T.L * k + c ∧ b ∣ T.L * k + c) := by
    refine Finset.filter_congr ?_
    intro k _
    simp [Finset.mem_insert]
  have h := T.crt_count hsub c
  rw [hfil, Finset.prod_pair hab] at h
  rw [h]
  push_cast
  ring

theorem crt_count_three {a b d : ℕ} (ha : a ∈ insert T.parent T.tagIndex)
    (hb : b ∈ insert T.parent T.tagIndex) (hd : d ∈ insert T.parent T.tagIndex)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (c : ℕ) :
    ((((Finset.range T.period).filter
        (fun k => a ∣ T.L * k + c ∧ b ∣ T.L * k + c ∧ d ∣ T.L * k + c)).card : ℕ) : ℝ)
      = (T.period : ℝ) / ((a : ℝ) * ((b : ℝ) * (d : ℝ))) := by
  classical
  have hsub : ({a, b, d} : Finset ℕ) ⊆ insert T.parent T.tagIndex := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact ha
    · rcases Finset.mem_insert.mp hx' with rfl | hx''
      · exact hb
      · rw [Finset.mem_singleton] at hx''
        exact hx'' ▸ hd
  have hfil : (Finset.range T.period).filter
        (fun k => ∀ x ∈ ({a, b, d} : Finset ℕ), x ∣ T.L * k + c)
      = (Finset.range T.period).filter
        (fun k => a ∣ T.L * k + c ∧ b ∣ T.L * k + c ∧ d ∣ T.L * k + c) := by
    refine Finset.filter_congr ?_
    intro k _
    simp [Finset.mem_insert]
  have hnotmem : a ∉ ({b, d} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨hab, had⟩
  have hprod : (∏ x ∈ ({a, b, d} : Finset ℕ), x) = a * (b * d) := by
    rw [Finset.prod_insert hnotmem, Finset.prod_pair hbd]
  have h := T.crt_count hsub c
  rw [hfil, hprod] at h
  rw [h]
  push_cast
  ring

/-! ### The conditional tag index and the paper's `Z_q` -/

theorem mem_condTags_iff {r p : ℕ} :
    p ∈ T.condTags r ↔ ∃ d ∈ T.L.divisors, d ∣ r ∧ p ∈ T.tags d := by
  classical
  unfold condTags
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨d, ⟨hd, hdr⟩, hpd⟩
    exact ⟨d, hd, hdr, hpd⟩
  · rintro ⟨d, hd, hdr, hpd⟩
    exact ⟨d, ⟨hd, hdr⟩, hpd⟩

theorem condTags_subset_tagIndex (r : ℕ) : T.condTags r ⊆ T.tagIndex := by
  intro p hp
  obtain ⟨d, hd, -, hpd⟩ := T.mem_condTags_iff.mp hp
  exact T.mem_tagIndex_iff.mpr ⟨d, hd, hpd⟩

/-- The paper's `μ_r = ∑_{d ∣ r} S_{q,d}`. -/
theorem sum_inv_condTags (r : ℕ) :
    (∑ p ∈ T.condTags r, 1 / (p : ℝ))
      = ∑ d ∈ T.L.divisors.filter (fun d => d ∣ r), ∑ p ∈ T.tags d, 1 / (p : ℝ) := by
  classical
  unfold condTags
  refine Finset.sum_biUnion ?_
  intro d hd d' hd' hne
  exact T.tag_disjoint d (Finset.mem_filter.mp (Finset.mem_coe.mp hd)).1
    d' (Finset.mem_filter.mp (Finset.mem_coe.mp hd')).1 hne

theorem coprime_divisor_tagIndex {d p : ℕ} (hd : d ∈ T.L.divisors) (hp : p ∈ T.tagIndex) :
    Nat.Coprime d p := by
  have hpp : p.Prime := T.tagIndex_prime hp
  have hnot : ¬ p ∣ d := fun h =>
    T.not_dvd_L_of_mem_tagIndex hp (h.trans (Nat.mem_divisors.mp hd).1)
  exact ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hnot).symm

/-- "Since `d ∣ N + r` is equivalent to `d ∣ r`", the paper's `Z_q(n)` counts
exactly the tag primes of `𝓘_q` whose divisor part divides `r`. -/
theorem tagCount_eq_condTags {r n : ℕ} (hn : ∀ d ∈ T.L.divisors, (d ∣ n ↔ d ∣ r)) :
    T.toParentTagData.tagCount n = ((T.condTags r).filter (fun p => p ∣ n)).card := by
  classical
  have hset : T.tagIndex.filter (fun p => T.tagModulus p ∣ n)
      = (T.condTags r).filter (fun p => p ∣ n) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hdvd⟩
      obtain ⟨d, hd, hpd⟩ := T.mem_tagIndex_iff.mp hp
      rw [T.tagModulus_eq hd hpd] at hdvd
      have hdn : d ∣ n := (dvd_mul_right d p).trans hdvd
      have hpn : p ∣ n := (dvd_mul_left p d).trans hdvd
      exact ⟨T.mem_condTags_iff.mpr ⟨d, hd, (hn d hd).mp hdn, hpd⟩, hpn⟩
    · rintro ⟨hp, hpn⟩
      obtain ⟨d, hd, hdr, hpd⟩ := T.mem_condTags_iff.mp hp
      have hpidx : p ∈ T.tagIndex := T.mem_tagIndex_iff.mpr ⟨d, hd, hpd⟩
      refine ⟨hpidx, ?_⟩
      rw [T.tagModulus_eq hd hpd]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (T.coprime_divisor_tagIndex hd hpidx)
        ((hn d hd).mpr hdr) hpn
  show (T.tagIndex.filter (fun p => T.tagModulus p ∣ n)).card = _
  rw [hset]

/-! ### The success events of one parent group -/

/-- The paper's success event at offset `r`, over one period of the sampling
`N = L k`: `q ∣ N + r` and `Z_q(N + r) ≥ r`. -/
def succSet (r : ℕ) : Finset ℕ :=
  (Finset.range T.period).filter (fun k =>
    T.parent ∣ T.L * k + (T.L + r) ∧
      r ≤ ((T.condTags r).filter (fun p => p ∣ T.L * k + (T.L + r))).card)

/-- The paper's `E_q`: success at some offset `r ∈ G`. -/
def parentSuccess (G : Finset ℕ) : Finset ℕ :=
  (Finset.range T.period).filter (fun k => ∃ r ∈ G,
    T.parent ∣ T.L * k + (T.L + r) ∧
      r ≤ ((T.condTags r).filter (fun p => p ∣ T.L * k + (T.L + r))).card)

/-- "Thus success has conditional probability at least `1/2`." -/
theorem period_div_two_parent_le_card_succSet {r : ℕ} (hr : r ∈ T.L.divisors)
    (hmu : 4 * (r : ℝ) ≤ ∑ p ∈ T.condTags r, 1 / (p : ℝ)) :
    (T.period : ℝ) / (2 * (T.parent : ℝ)) ≤ (((T.succSet r).card : ℕ) : ℝ) := by
  classical
  have hrpos : 0 < r := Nat.pos_of_mem_divisors hr
  have hqmem : T.parent ∈ insert T.parent T.tagIndex := Finset.mem_insert_self _ _
  have hSgsub : ∀ p ∈ T.condTags r, p ∈ insert T.parent T.tagIndex := fun p hp =>
    Finset.mem_insert_of_mem (T.condTags_subset_tagIndex r hp)
  have hSgne : ∀ p ∈ T.condTags r, T.parent ≠ p := by
    intro p hp h
    exact T.parent_notMem_tagIndex (h ▸ T.condTags_subset_tagIndex r hp)
  have hq0 : (0 : ℝ) < (T.parent : ℝ) := by exact_mod_cast T.parent_prime.pos
  have hAv2 : ∀ p : ℕ,
      ((Finset.range T.period).filter (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
          (fun k => p ∣ T.L * k + (T.L + r))
        = (Finset.range T.period).filter
          (fun k => T.parent ∣ T.L * k + (T.L + r) ∧ p ∣ T.L * k + (T.L + r)) := by
    intro p
    rw [Finset.filter_filter]
  have hOm : ((((Finset.range T.period).filter
        (fun k => T.parent ∣ T.L * k + (T.L + r))).card : ℕ) : ℝ)
      = (T.period : ℝ) / (T.parent : ℝ) := T.crt_count_one hqmem _
  have hA : ∀ p ∈ T.condTags r,
      ((Finset.range T.period).filter (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
          (fun k => p ∣ T.L * k + (T.L + r))
        ⊆ (Finset.range T.period).filter (fun k => T.parent ∣ T.L * k + (T.L + r)) :=
    fun p _ => Finset.filter_subset _ _
  have hmarg : ∀ p ∈ T.condTags r,
      (((((Finset.range T.period).filter (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
          (fun k => p ∣ T.L * k + (T.L + r))).card : ℕ) : ℝ)
        = ((((Finset.range T.period).filter
            (fun k => T.parent ∣ T.L * k + (T.L + r))).card : ℕ) : ℝ) * (1 / (p : ℝ)) := by
    intro p hp
    have hppos : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (T.tagIndex_prime (T.condTags_subset_tagIndex r hp)).pos
    rw [hAv2 p, T.crt_count_two hqmem (hSgsub p hp) (hSgne p hp) _, hOm]
    field_simp
  have hpair : ∀ p ∈ T.condTags r, ∀ p' ∈ T.condTags r, p ≠ p' →
      ((((((Finset.range T.period).filter
            (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
            (fun k => p ∣ T.L * k + (T.L + r)))
          ∩ (((Finset.range T.period).filter
            (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
            (fun k => p' ∣ T.L * k + (T.L + r)))).card : ℕ) : ℝ)
        = ((((Finset.range T.period).filter
            (fun k => T.parent ∣ T.L * k + (T.L + r))).card : ℕ) : ℝ)
          * ((1 / (p : ℝ)) * (1 / (p' : ℝ))) := by
    intro p hp p' hp' hne
    have hppos : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (T.tagIndex_prime (T.condTags_subset_tagIndex r hp)).pos
    have hp'pos : (0 : ℝ) < (p' : ℝ) := by
      exact_mod_cast (T.tagIndex_prime (T.condTags_subset_tagIndex r hp')).pos
    have hinter :
        ((((Finset.range T.period).filter (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
            (fun k => p ∣ T.L * k + (T.L + r)))
          ∩ (((Finset.range T.period).filter (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
            (fun k => p' ∣ T.L * k + (T.L + r))))
          = (Finset.range T.period).filter (fun k => T.parent ∣ T.L * k + (T.L + r)
              ∧ p ∣ T.L * k + (T.L + r) ∧ p' ∣ T.L * k + (T.L + r)) := by
      rw [hAv2 p, hAv2 p', ← Finset.filter_and]
      refine Finset.filter_congr ?_
      intro k _
      tauto
    rw [hinter, T.crt_count_three hqmem (hSgsub p hp) (hSgsub p' hp')
      (hSgne p hp) (hSgne p' hp') hne _, hOm]
    field_simp
  have hmain := half_card_le_card_filter_le
    ((Finset.range T.period).filter (fun k => T.parent ∣ T.L * k + (T.L + r)))
    (T.condTags r)
    (fun p => ((Finset.range T.period).filter
        (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
        (fun k => p ∣ T.L * k + (T.L + r)))
    r hrpos hA hmarg hpair hmu
  have hinner : ∀ k ∈ (Finset.range T.period).filter
        (fun k => T.parent ∣ T.L * k + (T.L + r)),
      (T.condTags r).filter (fun p => k ∈ ((Finset.range T.period).filter
          (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
          (fun k => p ∣ T.L * k + (T.L + r)))
        = (T.condTags r).filter (fun p => p ∣ T.L * k + (T.L + r)) := by
    intro k hk
    refine Finset.filter_congr ?_
    intro p _
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨hk, h⟩
  have hstep : ((Finset.range T.period).filter
        (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
        (fun k => r ≤ ((T.condTags r).filter (fun p =>
          k ∈ ((Finset.range T.period).filter
            (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
            (fun k => p ∣ T.L * k + (T.L + r)))).card)
      = T.succSet r := by
    have h1 : ((Finset.range T.period).filter
          (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
          (fun k => r ≤ ((T.condTags r).filter (fun p =>
            k ∈ ((Finset.range T.period).filter
              (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
              (fun k => p ∣ T.L * k + (T.L + r)))).card)
        = ((Finset.range T.period).filter
          (fun k => T.parent ∣ T.L * k + (T.L + r))).filter
          (fun k => r ≤ ((T.condTags r).filter
            (fun p => p ∣ T.L * k + (T.L + r))).card) := by
      refine Finset.filter_congr ?_
      intro k hk
      rw [hinner k hk]
    rw [h1]
    ext k
    constructor
    · intro hk
      have ha := Finset.mem_filter.mp hk
      have hb := Finset.mem_filter.mp ha.1
      exact Finset.mem_filter.mpr ⟨hb.1, hb.2, ha.2⟩
    · intro hk
      have ha := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ha.1, ha.2.1⟩, ha.2.2⟩
  rw [hstep, hOm] at hmain
  calc (T.period : ℝ) / (2 * (T.parent : ℝ))
      = (T.period : ℝ) / (T.parent : ℝ) / 2 := by
        field_simp
    _ ≤ _ := hmain

/-- "The event `E_q` of success for some `r ∈ G` consequently satisfies
`ℙ_L(E_q) ≥ |G|/(2q)`": for a fixed parent the events at distinct offsets are
disjoint, because `1 ≤ r ≤ L < q`. -/
theorem card_parentSuccess_ge (G : Finset ℕ) (hG : G ⊆ T.L.divisors)
    (hmu : ∀ r ∈ G, 4 * (r : ℝ) ≤ ∑ p ∈ T.condTags r, 1 / (p : ℝ)) :
    (G.card : ℝ) * ((T.period : ℝ) / (2 * (T.parent : ℝ)))
      ≤ (((T.parentSuccess G).card : ℕ) : ℝ) := by
  classical
  have hbounds : ∀ r ∈ G, 0 < r ∧ r ≤ T.L := by
    intro r hr
    exact ⟨Nat.pos_of_mem_divisors (hG hr),
      Nat.le_of_dvd T.L_pos (Nat.mem_divisors.mp (hG hr)).1⟩
  have hdisj : ∀ r ∈ G, ∀ r' ∈ G, r ≠ r' → Disjoint (T.succSet r) (T.succSet r') := by
    intro r hr r' hr' hne
    rw [Finset.disjoint_left]
    intro k hk hk'
    have h1 := (Finset.mem_filter.mp hk).2.1
    have h2 := (Finset.mem_filter.mp hk').2.1
    obtain ⟨hr0, hrL⟩ := hbounds r hr
    obtain ⟨hr'0, hr'L⟩ := hbounds r' hr'
    have hLq := T.L_lt_parent
    rcases Nat.lt_or_ge r r' with hlt | hge
    · have hsub : T.parent ∣ (T.L * k + (T.L + r')) - (T.L * k + (T.L + r)) :=
        Nat.dvd_sub h2 h1
      have heq : (T.L * k + (T.L + r')) - (T.L * k + (T.L + r)) = r' - r := by omega
      rw [heq] at hsub
      have hz : r' - r = 0 := Nat.eq_zero_of_dvd_of_lt hsub (by omega)
      omega
    · have hlt' : r' < r := by omega
      have hsub : T.parent ∣ (T.L * k + (T.L + r)) - (T.L * k + (T.L + r')) :=
        Nat.dvd_sub h1 h2
      have heq : (T.L * k + (T.L + r)) - (T.L * k + (T.L + r')) = r - r' := by omega
      rw [heq] at hsub
      have hz : r - r' = 0 := Nat.eq_zero_of_dvd_of_lt hsub (by omega)
      omega
  have hsub : G.biUnion (fun r => T.succSet r) ⊆ T.parentSuccess G := by
    intro k hk
    obtain ⟨r, hrG, hkr⟩ := Finset.mem_biUnion.mp hk
    have h := Finset.mem_filter.mp hkr
    exact Finset.mem_filter.mpr ⟨h.1, ⟨r, hrG, h.2.1, h.2.2⟩⟩
  have hcardU : (G.biUnion (fun r => T.succSet r)).card = ∑ r ∈ G, (T.succSet r).card :=
    Finset.card_biUnion hdisj
  have hle : (G.biUnion (fun r => T.succSet r)).card ≤ (T.parentSuccess G).card :=
    Finset.card_le_card hsub
  have hleR : ((∑ r ∈ G, (T.succSet r).card : ℕ) : ℝ) ≤ (((T.parentSuccess G).card : ℕ) : ℝ) := by
    rw [← hcardU]
    exact_mod_cast hle
  have hsumle : (G.card : ℝ) * ((T.period : ℝ) / (2 * (T.parent : ℝ)))
      ≤ ∑ r ∈ G, (((T.succSet r).card : ℕ) : ℝ) := by
    calc (G.card : ℝ) * ((T.period : ℝ) / (2 * (T.parent : ℝ)))
        = ∑ _r ∈ G, ((T.period : ℝ) / (2 * (T.parent : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun r hr =>
          T.period_div_two_parent_le_card_succSet (hG hr) (hmu r hr)
  have hcast : ((∑ r ∈ G, (T.succSet r).card : ℕ) : ℝ)
      = ∑ r ∈ G, (((T.succSet r).card : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at hleR
  linarith

/-! ### Periodicity of the success event -/

theorem dvd_linear_mod_period {a : ℕ} (ha : a ∈ insert T.parent T.tagIndex) (m c : ℕ) :
    (a ∣ T.L * (m % T.period) + c) ↔ (a ∣ T.L * m + c) := by
  have hmod : (m % T.period) % a = m % a :=
    Nat.mod_mod_of_dvd m (T.primeSet_dvd_period ha)
  have hme : T.L * (m % T.period) + c ≡ T.L * m + c [MOD a] :=
    Nat.ModEq.add_right c (Nat.ModEq.mul_left T.L hmod)
  constructor
  · intro h
    exact (Nat.modEq_zero_iff_dvd).mp (hme.symm.trans ((Nat.modEq_zero_iff_dvd).mpr h))
  · intro h
    exact (Nat.modEq_zero_iff_dvd).mp (hme.trans ((Nat.modEq_zero_iff_dvd).mpr h))

theorem condTags_filter_mod_period (r m : ℕ) :
    (T.condTags r).filter (fun p => p ∣ T.L * (m % T.period) + (T.L + r))
      = (T.condTags r).filter (fun p => p ∣ T.L * m + (T.L + r)) := by
  classical
  refine Finset.filter_congr ?_
  intro p hp
  exact T.dvd_linear_mod_period
    (Finset.mem_insert_of_mem (T.condTags_subset_tagIndex r hp)) m (T.L + r)

/-- The paper's "different parent groups depend on disjoint prime coordinates":
the success event of one parent depends on the sample only through its residue
modulo that parent's own period. -/
theorem success_mod_period (G : Finset ℕ) (m : ℕ) :
    ((∃ r ∈ G, T.parent ∣ T.L * (m % T.period) + (T.L + r) ∧
        r ≤ ((T.condTags r).filter
          (fun p => p ∣ T.L * (m % T.period) + (T.L + r))).card)
      ↔ (∃ r ∈ G, T.parent ∣ T.L * m + (T.L + r) ∧
        r ≤ ((T.condTags r).filter (fun p => p ∣ T.L * m + (T.L + r))).card)) := by
  classical
  have hq : T.parent ∈ insert T.parent T.tagIndex := Finset.mem_insert_self _ _
  constructor
  · rintro ⟨r, hrG, h1, h2⟩
    refine ⟨r, hrG, (T.dvd_linear_mod_period hq m (T.L + r)).mp h1, ?_⟩
    rwa [T.condTags_filter_mod_period r m] at h2
  · rintro ⟨r, hrG, h1, h2⟩
    refine ⟨r, hrG, (T.dvd_linear_mod_period hq m (T.L + r)).mpr h1, ?_⟩
    rwa [T.condTags_filter_mod_period r m]

/-! ### Squarefreeness and cross-parent disjointness -/

/-- "All exponents are squarefree": every exponent of `F_q` divides
`q · L · ∏_{p ∈ 𝓘_q} p`, a product of distinct primes. -/
theorem squarefree_of_mem_frame' (hLsq : Squarefree T.L)
    {a : ℕ} (ha : a ∈ T.toParentTagData.frame) : Squarefree a := by
  classical
  have hdvd : a ∣ T.parent * (T.L * primeProd T.tagIndex) := by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ha
    have hIsub : I ⊆ T.tagIndex := Finset.mem_powerset.mp hI
    refine mul_dvd_mul_left T.parent (Finset.lcm_dvd ?_)
    intro p hp
    obtain ⟨d, hd, hpd⟩ := T.mem_tagIndex_iff.mp (hIsub hp)
    show T.tagModulus p ∣ T.L * primeProd T.tagIndex
    rw [T.tagModulus_eq hd hpd]
    refine mul_dvd_mul (Nat.mem_divisors.mp hd).1 ?_
    unfold primeProd
    exact Finset.dvd_prod_of_mem (fun x => x) (hIsub hp)
  have hsqProd : Squarefree (primeProd T.tagIndex) :=
    primeProd_squarefree (fun p hp => T.tagIndex_prime hp)
  have hcopLP : Nat.Coprime T.L (primeProd T.tagIndex) := by
    unfold primeProd
    refine Nat.Coprime.prod_right ?_
    intro p hp
    exact ((Nat.Prime.coprime_iff_not_dvd (T.tagIndex_prime hp)).mpr
      (T.not_dvd_L_of_mem_tagIndex hp)).symm
  have hsq2 : Squarefree (T.L * primeProd T.tagIndex) :=
    Nat.squarefree_mul_iff.mpr ⟨hcopLP, hLsq, hsqProd⟩
  have hcopq : Nat.Coprime T.parent (T.L * primeProd T.tagIndex) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact (Nat.Prime.coprime_iff_not_dvd T.parent_prime).mpr T.parent_not_dvd_L
    · unfold primeProd
      exact Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes T.parent_prime (T.tagIndex_prime hp)).mpr
          (fun h => T.parent_notMem_tagIndex (h ▸ hp))
  exact (Nat.squarefree_mul_iff.mpr
    ⟨hcopq, T.parent_prime.squarefree, hsq2⟩).squarefree_of_dvd hdvd

/-- "Different parent primes give disjoint sets, since no parent prime occurs in
any other set." -/
theorem frame_disjoint {T T' : TagFamily} (hL : T'.L = T.L)
    (hne : T.parent ≠ T'.parent) (hnotin : T'.parent ∉ T.tagIndex) :
    Disjoint T.toParentTagData.frame T'.toParentTagData.frame := by
  classical
  rw [Finset.disjoint_left]
  intro a ha ha'
  have hq'a : T'.parent ∣ a := T'.toParentTagData.parent_dvd_of_mem_frame ha'
  have hadvd : a ∣ T.parent * ∏ i ∈ T.tagIndex, T.tagModulus i :=
    T.toParentTagData.dvd_parent_mul_prod ha
  have hdvd : T'.parent ∣ T.parent * ∏ i ∈ T.tagIndex, T.tagModulus i := hq'a.trans hadvd
  have hp' : Nat.Prime T'.parent := T'.parent_prime
  rcases (Nat.Prime.dvd_mul hp').mp hdvd with h | h
  · exact hne ((Nat.prime_dvd_prime_iff_eq hp' T.parent_prime).mp h).symm
  · obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finset_prod_iff hp'.prime T.tagModulus).mp h
    obtain ⟨d, hd, hid⟩ := T.mem_tagIndex_iff.mp hi
    rw [T.tagModulus_eq hd hid] at hdi
    rcases (Nat.Prime.dvd_mul hp').mp hdi with h1 | h2
    · exact (hL ▸ T'.parent_not_dvd_L) (h1.trans (Nat.mem_divisors.mp hd).1)
    · have heq : T'.parent = i := (Nat.prime_dvd_prime_iff_eq hp' (T.tagIndex_prime hi)).mp h2
      exact hnotin (heq ▸ hi)

end TagFamily

/-! ### The selected data of the whole construction -/

/-- A junk labelled-pair datum, used to make the family of parent groups a total
function on `ℕ`. -/
def trivialParentTagData : ParentTagData where
  parent := 2
  idx := ∅
  modulus := fun _ => 1
  tag := fun _ => 1
  parent_prime := Nat.prime_two
  tag_prime := by intro i hi; simp at hi
  tag_dvd_modulus := by intro i hi; simp at hi
  modulus_pos := by intro i hi; simp at hi
  tag_not_dvd_parent := by intro i hi; simp at hi
  tag_not_dvd_other := by intro i hi; simp at hi
  parent_coprime_modulus := by intro i hi; simp at hi

/-- The combinatorial data chosen in the first half of the paper's proof: the
squarefree modulus `L`, the parent primes `𝓑`, and the tag sets `T_{q,d}`.  The
numerical conditions (`B ≥ H²`, `4/D ≤ ∑ 1/q ≤ 5/D`, `4d/H ≤ S_{q,d} ≤ 5d/H`)
are carried as hypotheses of the individual estimates below, not as fields. -/
structure Selection where
  /-- The paper's integer `H ≥ 2`. -/
  Hn : ℕ
  /-- The paper's squarefree modulus `L`. -/
  Lv : ℕ
  /-- The paper's parent primes `𝓑`. -/
  parents : Finset ℕ
  /-- The paper's tag sets `T_{q,d}`, indexed by the pair `(q, d)`. -/
  tagSets : ℕ × ℕ → Finset ℕ
  Hn_two : 2 ≤ Hn
  Lv_pos : 0 < Lv
  Lv_squarefree : Squarefree Lv
  parents_nonempty : parents.Nonempty
  parents_prime : ∀ q ∈ parents, q.Prime
  parents_gt_Lv : ∀ q ∈ parents, Lv < q
  tag_prime : ∀ q ∈ parents, ∀ d ∈ Lv.divisors, ∀ p ∈ tagSets (q, d), p.Prime
  tag_ne_parent : ∀ q ∈ parents, ∀ d ∈ Lv.divisors, ∀ p ∈ tagSets (q, d),
    ∀ q' ∈ parents, p ≠ q'
  tag_not_dvd_Lv : ∀ q ∈ parents, ∀ d ∈ Lv.divisors, ∀ p ∈ tagSets (q, d), ¬ p ∣ Lv
  tag_disjoint : ∀ q ∈ parents, ∀ d ∈ Lv.divisors, ∀ q' ∈ parents, ∀ d' ∈ Lv.divisors,
    (q, d) ≠ (q', d') → Disjoint (tagSets (q, d)) (tagSets (q', d'))

/-- The arithmetic of "`ℙ_L(E_q) ≥ |G|/(2q) ≥ D/(4q)`", over plain reals. -/
theorem fail_bound_aux {Dv Gc per suc fal qr : ℝ} (hqr : 0 < qr) (hper : 0 ≤ per)
    (hDG : Dv ≤ 2 * Gc) (hsucc : Gc * (per / (2 * qr)) ≤ suc) (hadd : suc + fal = per) :
    fal ≤ per * (1 - Dv / (4 * qr)) := by
  have h3 : per * (Dv / (4 * qr)) = (Dv / 2) * (per / (2 * qr)) := by
    field_simp
    ring
  have hfac : (0 : ℝ) ≤ per / (2 * qr) := by positivity
  have h2 : (Dv / 2) * (per / (2 * qr)) ≤ Gc * (per / (2 * qr)) :=
    mul_le_mul_of_nonneg_right (by linarith) hfac
  have hexp : per * (1 - Dv / (4 * qr)) = per - per * (Dv / (4 * qr)) := by ring
  rw [hexp, h3]
  linarith

/-- The arithmetic of "`∑_q D/(4q) ≥ (D/4)(4/D) = 1`", over plain reals. -/
theorem one_le_quarter_mul {Dv S : ℝ} (hD : 0 < Dv) (hS : 4 / Dv ≤ S) :
    1 ≤ (Dv / 4) * S := by
  have h4 : (0 : ℝ) < Dv / 4 := by positivity
  have h5 := mul_le_mul_of_nonneg_left hS h4.le
  have h6 : (Dv / 4) * (4 / Dv) = 1 := by field_simp
  linarith

/-- A prime dividing `Q` but not the divisor `L` of `Q` divides `Q / L`. -/
theorem prime_dvd_div {a L Q : ℕ} (hp : a.Prime) (hnd : ¬ a ∣ L) (hL : 0 < L)
    (hLQ : L ∣ Q) (haQ : a ∣ Q) : a ∣ Q / L := by
  obtain ⟨t, ht⟩ := hLQ
  have hQt : Q / L = t := by rw [ht, Nat.mul_div_cancel_left _ hL]
  rw [hQt]
  rw [ht] at haQ
  rcases (Nat.Prime.dvd_mul hp).mp haQ with h | h
  · exact absurd h hnd
  · exact h

namespace Selection

variable (s : Selection)

/-- The parent group of `q ∈ 𝓑`, as a `TagFamily`. -/
def tagFam {q : ℕ} (hq : q ∈ s.parents) : TagFamily where
  L := s.Lv
  parent := q
  tags := fun d => s.tagSets (q, d)
  L_pos := s.Lv_pos
  parent_prime := s.parents_prime q hq
  L_lt_parent := s.parents_gt_Lv q hq
  tag_prime := fun d hd p hp => s.tag_prime q hq d hd p hp
  tag_ne_parent := fun d hd p hp => s.tag_ne_parent q hq d hd p hp q hq
  tag_not_dvd_L := fun d hd p hp => s.tag_not_dvd_Lv q hq d hd p hp
  tag_disjoint := fun d hd d' hd' hne =>
    s.tag_disjoint q hq d hd q hq d' hd' (fun h => hne (congrArg Prod.snd h))

/-- The family `q ↦ 𝓘_q` of labelled-pair data, total on `ℕ`. -/
def parentData (q : ℕ) : ParentTagData :=
  if h : q ∈ s.parents then (s.tagFam h).toParentTagData else trivialParentTagData

theorem parentData_eq {q : ℕ} (hq : q ∈ s.parents) :
    s.parentData q = (s.tagFam hq).toParentTagData := dif_pos hq

theorem parentData_parent {q : ℕ} (hq : q ∈ s.parents) : (s.parentData q).parent = q := by
  rw [s.parentData_eq hq]
  rfl

/-- The paper's `𝓘_q`, indexed by the tag prime. -/
def tagIndexOf (q : ℕ) : Finset ℕ := s.Lv.divisors.biUnion (fun d => s.tagSets (q, d))

/-- The labelled pairs of `𝓘_q` whose divisor part divides `r`. -/
def condTagsOf (q r : ℕ) : Finset ℕ :=
  (s.Lv.divisors.filter (fun d => d ∣ r)).biUnion (fun d => s.tagSets (q, d))

/-- The period `q ∏_{p ∈ 𝓘_q} p` of the sampling events of the parent `q`. -/
def periodOf (q : ℕ) : ℕ := q * primeProd (s.tagIndexOf q)

/-- The paper's `E_q`, as a set of residues modulo `periodOf q`. -/
def succSetOf (G : Finset ℕ) (q : ℕ) : Finset ℕ :=
  (Finset.range (s.periodOf q)).filter (fun k => ∃ r ∈ G,
    q ∣ s.Lv * k + (s.Lv + r) ∧
      r ≤ ((s.condTagsOf q r).filter (fun p => p ∣ s.Lv * k + (s.Lv + r))).card)

/-- The complement of `E_q` inside one period. -/
def failSetOf (G : Finset ℕ) (q : ℕ) : Finset ℕ :=
  (Finset.range (s.periodOf q)).filter (fun k => k ∉ s.succSetOf G q)

/-- The paper's support `F = ⋃_{q ∈ 𝓑} F_q`. -/
def support : Finset ℕ := s.parents.biUnion (fun q => (s.parentData q).frame)

/-- The sample points of one period at which some parent group succeeds. -/
def goodSet (G : Finset ℕ) (P0 : ℕ) : Finset ℕ :=
  (Finset.range P0).filter (fun m => ∃ q ∈ s.parents, ∃ r ∈ G,
    q ∣ s.Lv * m + (s.Lv + r) ∧
      r ≤ ((s.condTagsOf q r).filter (fun p => p ∣ s.Lv * m + (s.Lv + r))).card)

/-- The sample points at which every parent group fails. -/
def badSet (G : Finset ℕ) (P0 : ℕ) : Finset ℕ :=
  (Finset.range P0).filter (fun m => ∀ q ∈ s.parents, m % s.periodOf q ∈ s.failSetOf G q)

theorem tagFam_L {q : ℕ} (hq : q ∈ s.parents) : (s.tagFam hq).L = s.Lv := rfl

theorem tagFam_parent {q : ℕ} (hq : q ∈ s.parents) : (s.tagFam hq).parent = q := rfl

theorem tagFam_tagIndex {q : ℕ} (hq : q ∈ s.parents) :
    (s.tagFam hq).tagIndex = s.tagIndexOf q := rfl

theorem tagFam_condTags {q : ℕ} (hq : q ∈ s.parents) (r : ℕ) :
    (s.tagFam hq).condTags r = s.condTagsOf q r := rfl

theorem tagFam_period {q : ℕ} (hq : q ∈ s.parents) :
    (s.tagFam hq).period = s.periodOf q := rfl

theorem tagFam_parentSuccess {q : ℕ} (hq : q ∈ s.parents) (G : Finset ℕ) :
    (s.tagFam hq).parentSuccess G = s.succSetOf G q := rfl

theorem mem_tagIndexOf_iff {q p : ℕ} :
    p ∈ s.tagIndexOf q ↔ ∃ d ∈ s.Lv.divisors, p ∈ s.tagSets (q, d) :=
  Finset.mem_biUnion

theorem parent_notMem_tagIndexOf {q : ℕ} (hq : q ∈ s.parents) {q' : ℕ}
    (hq' : q' ∈ s.parents) : q' ∉ s.tagIndexOf q := by
  intro h
  obtain ⟨d, hd, hpd⟩ := s.mem_tagIndexOf_iff.mp h
  exact s.tag_ne_parent q hq d hd q' hpd q' hq' rfl

theorem frames_disjoint : ∀ q ∈ s.parents, ∀ q' ∈ s.parents, q ≠ q' →
    Disjoint (s.parentData q).frame (s.parentData q').frame := by
  intro q hq q' hq' hne
  rw [s.parentData_eq hq, s.parentData_eq hq']
  exact TagFamily.frame_disjoint rfl hne (s.parent_notMem_tagIndexOf hq hq')

theorem pos_of_mem_support {a : ℕ} (ha : a ∈ s.support) : 0 < a := by
  obtain ⟨q, -, haq⟩ := Finset.mem_biUnion.mp ha
  exact (s.parentData q).pos_of_mem_frame haq

theorem zero_notMem_support : (0 : ℕ) ∉ s.support := fun h =>
  absurd (s.pos_of_mem_support h) (lt_irrefl 0)

theorem parent_mem_frame' {q : ℕ} (hq : q ∈ s.parents) : q ∈ (s.parentData q).frame := by
  have h := (s.parentData q).parent_mem_frame
  rwa [s.parentData_parent hq] at h

theorem support_nonempty : s.support.Nonempty := by
  obtain ⟨q, hq⟩ := s.parents_nonempty
  exact ⟨q, Finset.mem_biUnion.mpr ⟨q, hq, s.parent_mem_frame' hq⟩⟩

theorem exists_parent_le_of_mem_support {a : ℕ} (ha : a ∈ s.support) :
    ∃ q ∈ s.parents, q ≤ a := by
  obtain ⟨q, hq, haq⟩ := Finset.mem_biUnion.mp ha
  refine ⟨q, hq, Nat.le_of_dvd ((s.parentData q).pos_of_mem_frame haq) ?_⟩
  have h := (s.parentData q).parent_dvd_of_mem_frame haq
  rwa [s.parentData_parent hq] at h

theorem squarefree_of_mem_support {a : ℕ} (ha : a ∈ s.support) : Squarefree a := by
  obtain ⟨q, hq, haq⟩ := Finset.mem_biUnion.mp ha
  rw [s.parentData_eq hq] at haq
  exact TagFamily.squarefree_of_mem_frame' _ s.Lv_squarefree haq

theorem parent_mem_support {q : ℕ} (hq : q ∈ s.parents) : q ∈ s.support :=
  Finset.mem_biUnion.mpr ⟨q, hq, s.parent_mem_frame' hq⟩

theorem parent_mul_tagModulus_mem_support {q : ℕ} (hq : q ∈ s.parents) {d p : ℕ}
    (hd : d ∈ s.Lv.divisors) (hp : p ∈ s.tagSets (q, d)) : q * (d * p) ∈ s.support := by
  have hmem : p ∈ (s.tagFam hq).tagIndex := (s.tagFam hq).mem_tagIndex_iff.mpr ⟨d, hd, hp⟩
  have h := (s.tagFam hq).toParentTagData.parent_mul_modulus_mem_frame hmem
  have hmod : (s.tagFam hq).tagModulus p = d * p := (s.tagFam hq).tagModulus_eq hd hp
  have h2 : q * (d * p) ∈ (s.tagFam hq).toParentTagData.frame := by
    rw [← hmod]
    exact h
  exact Finset.mem_biUnion.mpr ⟨q, hq, by rw [s.parentData_eq hq]; exact h2⟩

/-! ### The logarithmic cost of the whole support -/

theorem majorantCost_le {q : ℕ} (hq : q ∈ s.parents)
    (htag : ∀ d ∈ s.Lv.divisors, ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ)
      ≤ 5 * (d : ℝ) / (s.Hn : ℝ)) :
    (s.parentData q).majorantCost
      ≤ Real.log 2 / (q : ℝ) * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)) := by
  classical
  have hHr : (0 : ℝ) < (s.Hn : ℝ) := by
    have := s.Hn_two
    have : (2 : ℝ) ≤ (s.Hn : ℝ) := by exact_mod_cast this
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (s.parents_prime q hq).pos
  have hlog : (0 : ℝ) ≤ Real.log 2 / (q : ℝ) := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  rw [s.parentData_eq hq]
  have hmc : ((s.tagFam hq).toParentTagData).majorantCost
      = Real.log 2 / (q : ℝ)
        * (1 + ∑ p ∈ (s.tagFam hq).tagIndex, 1 / (((s.tagFam hq).tagModulus p : ℕ) : ℝ)) := rfl
  rw [hmc, (s.tagFam hq).sum_inv_tagModulus]
  refine mul_le_mul_of_nonneg_left ?_ hlog
  show (1 : ℝ) + ∑ d ∈ s.Lv.divisors, (1 / (d : ℝ)) * ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ)
      ≤ 1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)
  have hterm : ∀ d ∈ s.Lv.divisors,
      (1 / (d : ℝ)) * ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ) ≤ 5 / (s.Hn : ℝ) := by
    intro d hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have h1 : (1 / (d : ℝ)) * (∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ))
        ≤ (1 / (d : ℝ)) * (5 * (d : ℝ) / (s.Hn : ℝ)) :=
      mul_le_mul_of_nonneg_left (htag d hd) (by positivity)
    have h2 : (1 / (d : ℝ)) * (5 * (d : ℝ) / (s.Hn : ℝ)) = 5 / (s.Hn : ℝ) := by
      field_simp
    linarith
  have hbound : (∑ d ∈ s.Lv.divisors, (1 / (d : ℝ)) * ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ))
      ≤ 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ) := by
    calc (∑ d ∈ s.Lv.divisors, (1 / (d : ℝ)) * ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ))
        ≤ ∑ _d ∈ s.Lv.divisors, (5 / (s.Hn : ℝ)) := Finset.sum_le_sum hterm
      _ = (s.Lv.divisors.card : ℝ) * (5 / (s.Hn : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ) := by ring
  linarith

/-- The paper's `κ₁(F;1) ≤ (5 log 2 / D)(1 + 5D/H) ≤ 30 log 2 / H`. -/
theorem kappaOne_support_le
    (htag : ∀ q ∈ s.parents, ∀ d ∈ s.Lv.divisors,
      ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ) ≤ 5 * (d : ℝ) / (s.Hn : ℝ))
    (hsumB : ∑ q ∈ s.parents, 1 / (q : ℝ) ≤ 5 / (s.Lv.divisors.card : ℝ))
    (hHD : (s.Hn : ℝ) ≤ (s.Lv.divisors.card : ℝ)) :
    kappaOne s.support 1 ≤ 30 * Real.log 2 / (s.Hn : ℝ) := by
  classical
  have hHr : (0 : ℝ) < (s.Hn : ℝ) := by
    have h2 : (2 : ℝ) ≤ (s.Hn : ℝ) := by exact_mod_cast s.Hn_two
    linarith
  have hDr : (0 : ℝ) < (s.Lv.divisors.card : ℝ) := lt_of_lt_of_le hHr hHD
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hstep := kappaOne_biUnion_frame_le s.parents s.parentData s.frames_disjoint
  have hsum : (∑ q ∈ s.parents, (s.parentData q).majorantCost)
      ≤ ∑ q ∈ s.parents, Real.log 2 / (q : ℝ)
        * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)) :=
    Finset.sum_le_sum fun q hq => s.majorantCost_le hq (htag q hq)
  have hfac : (∑ q ∈ s.parents, Real.log 2 / (q : ℝ)
        * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)))
      = (Real.log 2 * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)))
        * ∑ q ∈ s.parents, 1 / (q : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hcoef : (0 : ℝ) ≤ Real.log 2 * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)) := by
    have : (0 : ℝ) ≤ 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ) := by positivity
    nlinarith
  have hfinal : (Real.log 2 * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)))
      * (∑ q ∈ s.parents, 1 / (q : ℝ))
      ≤ (Real.log 2 * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)))
        * (5 / (s.Lv.divisors.card : ℝ)) := mul_le_mul_of_nonneg_left hsumB hcoef
  have harith : (Real.log 2 * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)))
      * (5 / (s.Lv.divisors.card : ℝ))
      ≤ 30 * Real.log 2 / (s.Hn : ℝ) := by
    have hkey : (Real.log 2 * (1 + 5 * (s.Lv.divisors.card : ℝ) / (s.Hn : ℝ)))
        * (5 / (s.Lv.divisors.card : ℝ))
        = 5 * Real.log 2 / (s.Lv.divisors.card : ℝ) + 25 * Real.log 2 / (s.Hn : ℝ) := by
      field_simp
      ring
    have hmono : 5 * Real.log 2 / (s.Lv.divisors.card : ℝ) ≤ 5 * Real.log 2 / (s.Hn : ℝ) := by
      apply div_le_div_of_nonneg_left (by linarith) hHr hHD
    rw [hkey]
    have : 30 * Real.log 2 / (s.Hn : ℝ)
        = 5 * Real.log 2 / (s.Hn : ℝ) + 25 * Real.log 2 / (s.Hn : ℝ) := by ring
    rw [this]
    linarith
  have hsupport : s.support = s.parents.biUnion (fun q => (s.parentData q).frame) := rfl
  rw [hsupport]
  linarith

/-! ### The sampling period `Q/L` -/

theorem tagIndexOf_prime {q : ℕ} (hq : q ∈ s.parents) {p : ℕ} (hp : p ∈ s.tagIndexOf q) :
    p.Prime := by
  obtain ⟨d, hd, hpd⟩ := s.mem_tagIndexOf_iff.mp hp
  exact s.tag_prime q hq d hd p hpd

theorem tagIndexOf_not_dvd_Lv {q : ℕ} (hq : q ∈ s.parents) {p : ℕ}
    (hp : p ∈ s.tagIndexOf q) : ¬ p ∣ s.Lv := by
  obtain ⟨d, hd, hpd⟩ := s.mem_tagIndexOf_iff.mp hp
  exact s.tag_not_dvd_Lv q hq d hd p hpd

theorem parent_not_dvd_Lv {q : ℕ} (hq : q ∈ s.parents) : ¬ q ∣ s.Lv := by
  intro h
  have h1 := Nat.le_of_dvd s.Lv_pos h
  have h2 := s.parents_gt_Lv q hq
  omega

theorem primeSetOf_prime {q : ℕ} (hq : q ∈ s.parents) {a : ℕ}
    (ha : a ∈ insert q (s.tagIndexOf q)) : a.Prime := by
  rcases Finset.mem_insert.mp ha with rfl | h
  · exact s.parents_prime _ hq
  · exact s.tagIndexOf_prime hq h

theorem primeSetOf_not_dvd_Lv {q : ℕ} (hq : q ∈ s.parents) {a : ℕ}
    (ha : a ∈ insert q (s.tagIndexOf q)) : ¬ a ∣ s.Lv := by
  rcases Finset.mem_insert.mp ha with rfl | h
  · exact s.parent_not_dvd_Lv hq
  · exact s.tagIndexOf_not_dvd_Lv hq h

theorem primeSetOf_dvd_lcm {q : ℕ} (hq : q ∈ s.parents) {a : ℕ}
    (ha : a ∈ insert q (s.tagIndexOf q)) : a ∣ s.support.lcm id := by
  rcases Finset.mem_insert.mp ha with rfl | h
  · exact Finset.dvd_lcm (s.parent_mem_support hq)
  · obtain ⟨d, hd, hpd⟩ := s.mem_tagIndexOf_iff.mp h
    have hmem := s.parent_mul_tagModulus_mem_support hq hd hpd
    have hdd : a ∣ q * (d * a) := Dvd.dvd.mul_left (dvd_mul_left a d) q
    exact hdd.trans (Finset.dvd_lcm hmem)

theorem primeSetOf_dvd_quotient {q : ℕ} (hq : q ∈ s.parents)
    (hLdvd : s.Lv ∣ s.support.lcm id) {a : ℕ} (ha : a ∈ insert q (s.tagIndexOf q)) :
    a ∣ s.support.lcm id / s.Lv :=
  prime_dvd_div (s.primeSetOf_prime hq ha) (s.primeSetOf_not_dvd_Lv hq ha) s.Lv_pos
    hLdvd (s.primeSetOf_dvd_lcm hq ha)

theorem periodOf_eq_prod {q : ℕ} (hq : q ∈ s.parents) :
    s.periodOf q = ∏ a ∈ insert q (s.tagIndexOf q), a := by
  unfold periodOf primeProd
  rw [Finset.prod_insert (s.parent_notMem_tagIndexOf hq hq)]

theorem periodOf_pos {q : ℕ} (hq : q ∈ s.parents) : 0 < s.periodOf q := by
  unfold periodOf
  exact Nat.mul_pos (s.parents_prime q hq).pos
    (primeProd_pos (fun p hp => s.tagIndexOf_prime hq hp))

theorem periodOf_dvd_quotient {q : ℕ} (hq : q ∈ s.parents)
    (hLdvd : s.Lv ∣ s.support.lcm id) : s.periodOf q ∣ s.support.lcm id / s.Lv := by
  rw [s.periodOf_eq_prod hq]
  exact Finset.prod_primes_dvd _ (fun a ha => (s.primeSetOf_prime hq ha).prime)
    (fun a ha => s.primeSetOf_dvd_quotient hq hLdvd ha)

theorem tagIndexOf_disjoint {q q' : ℕ} (hq : q ∈ s.parents) (hq' : q' ∈ s.parents)
    (hne : q ≠ q') {p : ℕ} (hp : p ∈ s.tagIndexOf q) : p ∉ s.tagIndexOf q' := by
  intro hp'
  obtain ⟨d, hd, hpd⟩ := s.mem_tagIndexOf_iff.mp hp
  obtain ⟨d', hd', hpd'⟩ := s.mem_tagIndexOf_iff.mp hp'
  have hne2 : ((q, d) : ℕ × ℕ) ≠ (q', d') := fun h => hne (congrArg Prod.fst h)
  exact Finset.disjoint_left.mp (s.tag_disjoint q hq d hd q' hq' d' hd' hne2) hpd hpd'

theorem periodOf_coprime {q q' : ℕ} (hq : q ∈ s.parents) (hq' : q' ∈ s.parents)
    (hne : q ≠ q') : Nat.Coprime (s.periodOf q) (s.periodOf q') := by
  have hqp := s.parents_prime q hq
  have hq'p := s.parents_prime q' hq'
  have h1 : Nat.Coprime q q' := (Nat.coprime_primes hqp hq'p).mpr hne
  have h2 : Nat.Coprime q (primeProd (s.tagIndexOf q')) :=
    coprime_primeProd (fun p hp => s.tagIndexOf_prime hq' hp) hqp
      (s.parent_notMem_tagIndexOf hq' hq)
  have h3 : Nat.Coprime (primeProd (s.tagIndexOf q)) q' :=
    (coprime_primeProd (fun p hp => s.tagIndexOf_prime hq hp) hq'p
      (s.parent_notMem_tagIndexOf hq hq')).symm
  have h4 : Nat.Coprime (primeProd (s.tagIndexOf q)) (primeProd (s.tagIndexOf q')) := by
    unfold primeProd
    refine Nat.Coprime.prod_left ?_
    intro p hp
    exact coprime_primeProd (fun x hx => s.tagIndexOf_prime hq' hx)
      (s.tagIndexOf_prime hq hp) (s.tagIndexOf_disjoint hq hq' hne hp)
  unfold periodOf
  exact Nat.Coprime.mul (Nat.Coprime.mul_right h1 h2) (Nat.Coprime.mul_right h3 h4)

theorem prod_periodOf_dvd_quotient (hLdvd : s.Lv ∣ s.support.lcm id) :
    (∏ q ∈ s.parents, s.periodOf q) ∣ s.support.lcm id / s.Lv :=
  prod_dvd_of_pairwise_coprime s.parents s.periodOf
    (fun q hq q' hq' hne => s.periodOf_coprime hq hq' hne)
    (fun q hq => s.periodOf_dvd_quotient hq hLdvd)

/-- "The nonempty tag sets with `d = L` also show `L ∣ Q`." -/
theorem Lv_dvd_lcm {q : ℕ} (hq : q ∈ s.parents) {p : ℕ} (hp : p ∈ s.tagSets (q, s.Lv)) :
    s.Lv ∣ s.support.lcm id := by
  have hdL : s.Lv ∈ s.Lv.divisors := Nat.mem_divisors_self _ s.Lv_pos.ne'
  have hmem := s.parent_mul_tagModulus_mem_support hq hdL hp
  have h1 : s.Lv ∣ q * (s.Lv * p) := Dvd.dvd.mul_left (dvd_mul_right s.Lv p) q
  exact h1.trans (Finset.dvd_lcm hmem)

/-! ### The success probability of one parent group -/

theorem card_succSetOf_ge {q : ℕ} (hq : q ∈ s.parents) (G : Finset ℕ)
    (hG : G ⊆ s.Lv.divisors)
    (hmu : ∀ r ∈ G, 4 * (r : ℝ) ≤ ∑ d ∈ s.Lv.divisors.filter (fun d => d ∣ r),
      ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ)) :
    (G.card : ℝ) * ((s.periodOf q : ℝ) / (2 * (q : ℝ)))
      ≤ (((s.succSetOf G q).card : ℕ) : ℝ) := by
  have hmu' : ∀ r ∈ G, 4 * (r : ℝ) ≤ ∑ p ∈ (s.tagFam hq).condTags r, 1 / (p : ℝ) := by
    intro r hr
    rw [(s.tagFam hq).sum_inv_condTags r]
    exact hmu r hr
  have h := (s.tagFam hq).card_parentSuccess_ge G hG hmu'
  rw [s.tagFam_parentSuccess hq G] at h
  exact h

theorem succSetOf_subset (G : Finset ℕ) (q : ℕ) :
    s.succSetOf G q ⊆ Finset.range (s.periodOf q) := Finset.filter_subset _ _

theorem card_succ_add_card_fail (G : Finset ℕ) (q : ℕ) :
    (s.succSetOf G q).card + (s.failSetOf G q).card = s.periodOf q := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (s.periodOf q))
    (fun k => k ∈ s.succSetOf G q)
  rw [Finset.card_range] at h
  have h2 : (Finset.range (s.periodOf q)).filter (fun k => k ∈ s.succSetOf G q)
      = s.succSetOf G q := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (s.succSetOf_subset G q)]
  rw [h2] at h
  exact h

theorem mem_failSetOf_iff (G : Finset ℕ) {q : ℕ} (hq : q ∈ s.parents) (m : ℕ) :
    (m % s.periodOf q ∈ s.failSetOf G q)
      ↔ ¬ (∃ r ∈ G, q ∣ s.Lv * m + (s.Lv + r) ∧
          r ≤ ((s.condTagsOf q r).filter (fun p => p ∣ s.Lv * m + (s.Lv + r))).card) := by
  classical
  have hpos : 0 < s.periodOf q := s.periodOf_pos hq
  have hlt : m % s.periodOf q < s.periodOf q := Nat.mod_lt _ hpos
  constructor
  · intro h hcon
    refine (Finset.mem_filter.mp h).2 ?_
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,
      ((s.tagFam hq).success_mod_period G m).mpr hcon⟩
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, ?_⟩
    intro hc
    exact h (((s.tagFam hq).success_mod_period G m).mp (Finset.mem_filter.mp hc).2)

theorem card_good_add_card_bad (G : Finset ℕ) (P0 : ℕ) :
    (s.goodSet G P0).card + (s.badSet G P0).card = P0 := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range P0)
    (fun m => ∃ q ∈ s.parents, ∃ r ∈ G, q ∣ s.Lv * m + (s.Lv + r) ∧
      r ≤ ((s.condTagsOf q r).filter (fun p => p ∣ s.Lv * m + (s.Lv + r))).card)
  rw [Finset.card_range] at h
  have hbad : (Finset.range P0).filter (fun m => ¬ ∃ q ∈ s.parents, ∃ r ∈ G,
      q ∣ s.Lv * m + (s.Lv + r) ∧
        r ≤ ((s.condTagsOf q r).filter (fun p => p ∣ s.Lv * m + (s.Lv + r))).card)
      = s.badSet G P0 := by
    refine Finset.filter_congr ?_
    intro m _
    constructor
    · intro hn q hq
      refine (s.mem_failSetOf_iff G hq m).mpr ?_
      intro hc
      exact hn ⟨q, hq, hc⟩
    · rintro hall ⟨q, hq, hc⟩
      exact (s.mem_failSetOf_iff G hq m).mp (hall q hq) hc
  rw [hbad] at h
  exact h

/-! ### Success forces `U_F > 1` -/

theorem one_lt_framePotential_of_success {G : Finset ℕ} (hG : G ⊆ s.Lv.divisors)
    {q : ℕ} (hq : q ∈ s.parents) {m r : ℕ} (hr : r ∈ G)
    (h1 : q ∣ s.Lv * m + (s.Lv + r))
    (h2 : r ≤ ((s.condTagsOf q r).filter (fun p => p ∣ s.Lv * m + (s.Lv + r))).card) :
    1 < framePotential s.support (s.Lv * m + s.Lv) := by
  classical
  have hrpos : 0 < r := Nat.pos_of_mem_divisors (hG hr)
  have hqpos : 0 < q := (s.parents_prime q hq).pos
  obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  subst hr'
  have hidxA : s.Lv * m + s.Lv + r' + 1 = s.Lv * m + (s.Lv + (r' + 1)) := by ring
  have hidxB : s.Lv * m + s.Lv + (r' + q) + 1 = s.Lv * m + (s.Lv + (r' + 1)) + q := by ring
  have hdiv : ∀ d ∈ s.Lv.divisors,
      (d ∣ s.Lv * m + (s.Lv + (r' + 1)) ↔ d ∣ r' + 1) := by
    intro d hd
    have hdL : d ∣ s.Lv := (Nat.mem_divisors.mp hd).1
    have hdN : d ∣ s.Lv * m + s.Lv := Nat.dvd_add (Dvd.dvd.mul_right hdL m) hdL
    have hAx : s.Lv * m + (s.Lv + (r' + 1)) = (s.Lv * m + s.Lv) + (r' + 1) := by ring
    rw [hAx]
    constructor
    · intro h
      have h3 := Nat.dvd_sub h hdN
      simpa using h3
    · intro h
      exact Nat.dvd_add hdN h
  have htc : (s.tagFam hq).toParentTagData.tagCount (s.Lv * m + (s.Lv + (r' + 1)))
      = ((s.condTagsOf q (r' + 1)).filter
          (fun p => p ∣ s.Lv * m + (s.Lv + (r' + 1)))).card :=
    (s.tagFam hq).tagCount_eq_condTags hdiv
  have hcount : r' + 1
      ≤ (s.tagFam hq).toParentTagData.tagCount (s.Lv * m + (s.Lv + (r' + 1))) := by
    rw [htc]
    exact h2
  have hif := (s.tagFam hq).toParentTagData.incidenceCount_frame
    (s.Lv * m + (s.Lv + (r' + 1)))
  have hpar : (s.tagFam hq).toParentTagData.parent ∣ s.Lv * m + (s.Lv + (r' + 1)) := h1
  rw [if_pos hpar] at hif
  have h2r : 2 ^ (r' + 1)
      ≤ incidenceCount ((s.parentData q).frame) (s.Lv * m + (s.Lv + (r' + 1))) := by
    rw [s.parentData_eq hq, hif]
    exact Nat.pow_le_pow_right (by norm_num) hcount
  have hsubF : (s.parentData q).frame ⊆ s.support := fun a ha =>
    Finset.mem_biUnion.mpr ⟨q, hq, ha⟩
  have hmono : ∀ n, incidenceCount ((s.parentData q).frame) n ≤ incidenceCount s.support n := by
    intro n
    exact Finset.card_le_card (Finset.filter_subset_filter _ hsubF)
  have hfA : 2 ^ (r' + 1) ≤ incidenceCount s.support (s.Lv * m + (s.Lv + (r' + 1))) :=
    le_trans h2r (hmono _)
  have hfB : 1 ≤ incidenceCount s.support (s.Lv * m + (s.Lv + (r' + 1)) + q) := by
    unfold incidenceCount
    refine Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨s.parent_mem_support hq, ?_⟩⟩
    exact Nat.dvd_add h1 (dvd_refl q)
  have hA1 : (2 : ℝ) ^ (r' + 1)
      ≤ (incidenceCount s.support (s.Lv * m + s.Lv + r' + 1) : ℝ) := by
    rw [hidxA]
    exact_mod_cast hfA
  have hB1 : (1 : ℝ)
      ≤ (incidenceCount s.support (s.Lv * m + s.Lv + (r' + q) + 1) : ℝ) := by
    rw [hidxB]
    exact_mod_cast hfB
  have hterm1 : (1 : ℝ)
      ≤ (1 / 2 : ℝ) ^ (r' + 1) * (incidenceCount s.support (s.Lv * m + s.Lv + r' + 1) : ℝ) := by
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (r' + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hA1 hp.le
    have hid : (1 / 2 : ℝ) ^ (r' + 1) * (2 : ℝ) ^ (r' + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    linarith
  have hterm2 : (0 : ℝ)
      < (1 / 2 : ℝ) ^ (r' + q + 1)
        * (incidenceCount s.support (s.Lv * m + s.Lv + (r' + q) + 1) : ℝ) := by
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ (r' + q + 1) := by positivity
    nlinarith [hB1, hp]
  have hnonneg : ∀ j : ℕ, (0 : ℝ)
      ≤ (1 / 2 : ℝ) ^ (j + 1) * (incidenceCount s.support (s.Lv * m + s.Lv + j + 1) : ℝ) := by
    intro j
    positivity
  have hsubset : ({r', r' + q} : Finset ℕ) ⊆ Finset.range (r' + 1 + q) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)
  have hnepair : r' ≠ r' + q := by omega
  have hpairle := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (f := fun j => (1 / 2 : ℝ) ^ (j + 1)
      * (incidenceCount s.support (s.Lv * m + s.Lv + j + 1) : ℝ))
    (fun j _ _ => hnonneg j)
  rw [Finset.sum_pair hnepair] at hpairle
  have hpart := framePotential_eq_partial s.support s.zero_notMem_support
    (s.Lv * m + s.Lv) (r' + 1 + q)
  have htail : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (r' + 1 + q)
      * framePotential s.support (s.Lv * m + s.Lv + (r' + 1 + q)) :=
    mul_nonneg (by positivity) (framePotential_nonneg _ _)
  linarith

/-! ### The paper's `ℙ_L(U_F > 1) ≥ 1 - e^{-1}` -/

theorem condExceedProb_support_ge (G : Finset ℕ)
    (hG : G ⊆ s.Lv.divisors)
    (hGcard : (s.Lv.divisors.card : ℝ) ≤ 2 * (G.card : ℝ))
    (hmu : ∀ q ∈ s.parents, ∀ r ∈ G,
      4 * (r : ℝ) ≤ ∑ d ∈ s.Lv.divisors.filter (fun d => d ∣ r),
        ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ))
    (hqD : ∀ q ∈ s.parents, (s.Lv.divisors.card : ℝ) ≤ (q : ℝ))
    (hsumB : 4 / (s.Lv.divisors.card : ℝ) ≤ ∑ q ∈ s.parents, 1 / (q : ℝ))
    (hLdvd : s.Lv ∣ s.support.lcm id) :
    1 - Real.exp (-1) ≤ condExceedProb s.support s.Lv := by
  classical
  have hD0 : (0 : ℝ) < (s.Lv.divisors.card : ℝ) := by
    have : 0 < s.Lv.divisors.card :=
      Finset.card_pos.mpr ⟨s.Lv, Nat.mem_divisors_self _ s.Lv_pos.ne'⟩
    exact_mod_cast this
  obtain ⟨P0, hP0⟩ := hLdvd
  have hQne : s.support.lcm id ≠ 0 := frameLcm_ne_zero s.zero_notMem_support
  have hP0pos : 0 < P0 := by
    rcases Nat.eq_zero_or_pos P0 with h | h
    · exact absurd (by rw [hP0, h, Nat.mul_zero]) hQne
    · exact h
  have hP0R : (0 : ℝ) < (P0 : ℝ) := by exact_mod_cast hP0pos
  have hQdiv : s.support.lcm id / s.Lv = P0 := by
    rw [hP0, Nat.mul_div_cancel_left _ s.Lv_pos]
  have hperiodDvd : (∏ q ∈ s.parents, s.periodOf q) ∣ P0 := by
    have h := s.prod_periodOf_dvd_quotient ⟨P0, hP0⟩
    rwa [hQdiv] at h
  -- the independence count
  have hfilfail : ∀ q : ℕ, (Finset.range (s.periodOf q)).filter
      (fun x => x ∈ s.failSetOf G q) = s.failSetOf G q := by
    intro q
    rw [Finset.filter_mem_eq_inter]
    exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  have hcount0 := card_filter_forall_mod_mem s.parents s.periodOf (s.failSetOf G)
    (fun q hq => s.periodOf_pos hq)
    (fun q hq q' hq' hne => s.periodOf_coprime hq hq' hne) hperiodDvd
  have hcount : (s.badSet G P0).card * (∏ q ∈ s.parents, s.periodOf q)
      = P0 * ∏ q ∈ s.parents, (s.failSetOf G q).card := by
    have hfix : P0 * ∏ q ∈ s.parents,
        ((Finset.range (s.periodOf q)).filter (fun x => x ∈ s.failSetOf G q)).card
        = P0 * ∏ q ∈ s.parents, (s.failSetOf G q).card := by
      congr 1
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [hfilfail q]
    rw [← hfix]
    exact hcount0
  -- per-parent failure bound
  have hfailbound : ∀ q ∈ s.parents, ((s.failSetOf G q).card : ℝ)
      ≤ (s.periodOf q : ℝ) * (1 - (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ))) := by
    intro q hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (s.parents_prime q hq).pos
    have hsucc := s.card_succSetOf_ge hq G hG (fun r hr => hmu q hq r hr)
    have hadd : (((s.succSetOf G q).card : ℕ) : ℝ) + (((s.failSetOf G q).card : ℕ) : ℝ)
        = (s.periodOf q : ℝ) := by exact_mod_cast s.card_succ_add_card_fail G q
    exact fail_bound_aux hqpos (Nat.cast_nonneg _) hGcard hsucc hadd
  -- the exponential bound
  have hxle : ∀ q ∈ s.parents, (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ)) ≤ 1 := by
    intro q hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (s.parents_prime q hq).pos
    have hle := hqD q hq
    rw [div_le_one (by linarith)]
    linarith
  have hsumeq : (∑ q ∈ s.parents, (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ)))
      = ((s.Lv.divisors.card : ℝ) / 4) * ∑ q ∈ s.parents, 1 / (q : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_one_div, div_div]
  have hone : (1 : ℝ) ≤ ∑ q ∈ s.parents, (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ)) := by
    rw [hsumeq]
    exact one_le_quarter_mul hD0 hsumB
  have hprodfail : (∏ q ∈ s.parents, (((s.failSetOf G q).card : ℕ) : ℝ))
      ≤ (∏ q ∈ s.parents, (s.periodOf q : ℝ)) * Real.exp (-1) := by
    have hstep1 : (∏ q ∈ s.parents, (((s.failSetOf G q).card : ℕ) : ℝ))
        ≤ ∏ q ∈ s.parents, ((s.periodOf q : ℝ)
            * (1 - (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ)))) :=
      Finset.prod_le_prod (fun q _ => Nat.cast_nonneg _) hfailbound
    have hstep2 : (∏ q ∈ s.parents, ((s.periodOf q : ℝ)
          * (1 - (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ)))))
        = (∏ q ∈ s.parents, (s.periodOf q : ℝ))
          * ∏ q ∈ s.parents, (1 - (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ))) :=
      Finset.prod_mul_distrib
    have hstep3 : (∏ q ∈ s.parents, (1 - (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ))))
        ≤ Real.exp (-∑ q ∈ s.parents, (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ))) :=
      prod_one_sub_le_exp_neg_sum s.parents _ hxle
    have hstep4 : Real.exp (-∑ q ∈ s.parents, (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ)))
        ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have hpernn : (0 : ℝ) ≤ ∏ q ∈ s.parents, (s.periodOf q : ℝ) :=
      Finset.prod_nonneg fun q _ => Nat.cast_nonneg _
    calc (∏ q ∈ s.parents, (((s.failSetOf G q).card : ℕ) : ℝ))
        ≤ (∏ q ∈ s.parents, (s.periodOf q : ℝ))
            * ∏ q ∈ s.parents, (1 - (s.Lv.divisors.card : ℝ) / (4 * (q : ℝ))) := by
          rw [← hstep2]; exact hstep1
      _ ≤ (∏ q ∈ s.parents, (s.periodOf q : ℝ)) * Real.exp (-1) :=
          mul_le_mul_of_nonneg_left (le_trans hstep3 hstep4) hpernn
  -- transfer to the bad set
  have hprodpos : (0 : ℝ) < ∏ q ∈ s.parents, (s.periodOf q : ℝ) :=
    Finset.prod_pos fun q hq => by exact_mod_cast s.periodOf_pos hq
  have hcountR : (((s.badSet G P0).card : ℕ) : ℝ) * ∏ q ∈ s.parents, (s.periodOf q : ℝ)
      = (P0 : ℝ) * ∏ q ∈ s.parents, (((s.failSetOf G q).card : ℕ) : ℝ) := by
    have h : ((((s.badSet G P0).card * ∏ q ∈ s.parents, s.periodOf q : ℕ)) : ℝ)
        = (((P0 * ∏ q ∈ s.parents, (s.failSetOf G q).card : ℕ)) : ℝ) := by
      rw [hcount]
    push_cast at h
    exact h
  have hbadle : (((s.badSet G P0).card : ℕ) : ℝ) ≤ (P0 : ℝ) * Real.exp (-1) := by
    have h1 : (((s.badSet G P0).card : ℕ) : ℝ) * ∏ q ∈ s.parents, (s.periodOf q : ℝ)
        ≤ (P0 : ℝ) * ((∏ q ∈ s.parents, (s.periodOf q : ℝ)) * Real.exp (-1)) := by
      rw [hcountR]
      exact mul_le_mul_of_nonneg_left hprodfail hP0R.le
    have h2 : (((s.badSet G P0).card : ℕ) : ℝ) * ∏ q ∈ s.parents, (s.periodOf q : ℝ)
        ≤ ((P0 : ℝ) * Real.exp (-1)) * ∏ q ∈ s.parents, (s.periodOf q : ℝ) := by
      calc _ ≤ (P0 : ℝ) * ((∏ q ∈ s.parents, (s.periodOf q : ℝ)) * Real.exp (-1)) := h1
        _ = ((P0 : ℝ) * Real.exp (-1)) * ∏ q ∈ s.parents, (s.periodOf q : ℝ) := by ring
    exact le_of_mul_le_mul_right h2 hprodpos
  -- the good set
  have hgb : (((s.goodSet G P0).card : ℕ) : ℝ) + (((s.badSet G P0).card : ℕ) : ℝ)
      = (P0 : ℝ) := by exact_mod_cast s.card_good_add_card_bad G P0
  have hgood : (P0 : ℝ) * (1 - Real.exp (-1)) ≤ (((s.goodSet G P0).card : ℕ) : ℝ) := by
    have : (P0 : ℝ) * (1 - Real.exp (-1)) = (P0 : ℝ) - (P0 : ℝ) * Real.exp (-1) := by ring
    rw [this]
    linarith
  -- the conditional mean
  have hcond : condExceedProb s.support s.Lv
      = (∑ m ∈ Finset.range P0, exceedInd s.support ((m + 1) * s.Lv)) / (P0 : ℝ) := by
    unfold condExceedProb progressionMean
    rw [hQdiv]
  have hone' : ∀ m ∈ s.goodSet G P0, exceedInd s.support ((m + 1) * s.Lv) = 1 := by
    intro m hm
    obtain ⟨q, hq, r, hr, h1, h2⟩ := (Finset.mem_filter.mp hm).2
    have hgt := s.one_lt_framePotential_of_success hG hq hr h1 h2
    have hidx : (m + 1) * s.Lv = s.Lv * m + s.Lv := by ring
    unfold exceedInd
    rw [hidx, if_pos hgt]
  have hsumge : (((s.goodSet G P0).card : ℕ) : ℝ)
      ≤ ∑ m ∈ Finset.range P0, exceedInd s.support ((m + 1) * s.Lv) := by
    calc (((s.goodSet G P0).card : ℕ) : ℝ)
        = ∑ _m ∈ s.goodSet G P0, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ m ∈ s.goodSet G P0, exceedInd s.support ((m + 1) * s.Lv) :=
          (Finset.sum_congr rfl hone').symm
      _ ≤ ∑ m ∈ Finset.range P0, exceedInd s.support ((m + 1) * s.Lv) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun m _ _ => exceedInd_nonneg _ _)
  rw [hcond, le_div_iff₀ hP0R]
  calc (1 - Real.exp (-1)) * (P0 : ℝ) = (P0 : ℝ) * (1 - Real.exp (-1)) := by ring
    _ ≤ (((s.goodSet G P0).card : ℕ) : ℝ) := hgood
    _ ≤ _ := hsumge

end Selection

/-! ### Numerical auxiliaries for the selection -/

theorem sum_five_div_aux {Dv bv S : ℝ} (hD : 0 < Dv) (hb : 0 < bv) (hDb : Dv ≤ bv)
    (h : S ≤ 4 / Dv + 1 / bv) : S ≤ 5 / Dv := by
  have h1 : 1 / bv ≤ 1 / Dv := by
    rw [div_le_div_iff₀ hb hD]
    linarith
  have h2 : 4 / Dv + 1 / Dv = 5 / Dv := by ring
  linarith

theorem tag_sum_upper_aux {Hr dr S : ℝ} (hH : 0 < Hr) (hd : 1 ≤ dr)
    (h : S ≤ 4 * dr / Hr + 1 / Hr) : S ≤ 5 * dr / Hr := by
  have h1 : (1 : ℝ) / Hr ≤ dr / Hr := by
    rw [div_le_div_iff₀ hH hH]
    nlinarith
  have h2 : 4 * dr / Hr + dr / Hr = 5 * dr / Hr := by ring
  linarith

theorem mu_lower_aux {Hr rr sg : ℝ} (hH : 0 < Hr) (hsig : Hr * rr ≤ sg) :
    4 * rr ≤ 4 * sg / Hr := by
  rw [le_div_iff₀ hH]
  nlinarith

theorem exp_neg_one_lt_three_eighths : Real.exp (-1) < 3 / 8 := by
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ hpos (by norm_num)]
  linarith

theorem divisors_filter_dvd {L r : ℕ} (hr : r ∈ L.divisors) :
    L.divisors.filter (fun d => d ∣ r) = r.divisors := by
  classical
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨-, hdr⟩
    exact ⟨hdr, (Nat.pos_of_mem_divisors hr).ne'⟩
  · rintro ⟨hdr, -⟩
    obtain ⟨hrL, hL0⟩ := Nat.mem_divisors.mp hr
    exact ⟨⟨hdr.trans hrL, hL0⟩, hdr⟩

theorem kappaOne_nonneg (F : Finset ℕ) : 0 ≤ kappaOne F 1 := by
  refine le_csInf (logMajorantCosts_nonempty F one_pos) ?_
  rintro K ⟨c, hc0, -, rfl⟩
  exact divisorMajorantCost_nonneg hc0

/-! ### The theorem -/

/-- Long `thm` "arithmetic logarithmic counterexample"
(`paper/reasoning-parts/erdos257/a257_front.tex:9212`), clauses (i)-(iv).

For every integer `H ≥ 2` and every real `A₀ ≥ 0` there are a squarefree `L > 0`
and a finite nonempty set `F` of distinct squarefree positive integers with

* `min F > max {L, A₀}`,
* `κ₁(F;1) ≤ 30 log 2 / H`,
* `ℙ_L(U_F > 1) ≥ 1 - e^{-1}`,
* `𝒟_{L;R,L} 1_{U_F > 1} > 1/2` for some `R ≥ 0`.

The extra clause `L ∣ lcm F` is the paper's "since `L ∣ Q`", used by the
corollary. -/
theorem arithmetic_logarithmic_counterexample (H : ℕ) (hH : 2 ≤ H) (A₀ : ℝ) (hA₀ : 0 ≤ A₀) :
    ∃ (L : ℕ) (F : Finset ℕ),
      0 < L ∧ Squarefree L ∧ F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      (∀ a ∈ F, 0 < a ∧ Squarefree a) ∧
      (∀ a ∈ F, max (L : ℝ) A₀ < (a : ℝ)) ∧
      L ∣ F.lcm id ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) ∧
      1 - Real.exp (-1) ≤ condExceedProb F L ∧
      ∃ R : ℕ, 1 / 2 < dyadicMean L R L (exceedInd F) := by
  classical
  have hH0 : 0 < H := by omega
  have hHR : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
  -- the primes `P` and the modulus `L`
  obtain ⟨Ps, hPfresh, hPprod⟩ :=
    exists_freshPrimes_prod_one_add_inv_ge 1 Nat.one_pos ∅ ((H : ℝ) ^ 2)
  have hPprime : ∀ p ∈ Ps, p.Prime := fun p hp => (hPfresh p hp).1
  obtain ⟨Lv, hLvdef⟩ : ∃ Lv : ℕ, Lv = primeProd Ps := ⟨_, rfl⟩
  have hLvpos : 0 < Lv := by rw [hLvdef]; exact primeProd_pos hPprime
  have hLvsq : Squarefree Lv := by rw [hLvdef]; exact primeProd_squarefree hPprime
  have hsigma : (H : ℝ) ^ 2 ≤ sigmaRatio Lv := by
    rw [hLvdef, sigmaRatio_primeProd hPprime]
    exact hPprod
  have hDge : (H : ℝ) ^ 2 ≤ (Lv.divisors.card : ℝ) := by
    refine le_trans hsigma ?_
    rw [hLvdef]
    exact sigmaRatio_primeProd_le_card_divisors hPprime
  have hD0 : (0 : ℝ) < (Lv.divisors.card : ℝ) := by nlinarith
  have hHD : (H : ℝ) ≤ (Lv.divisors.card : ℝ) := by nlinarith
  have hDnat : Lv.divisors.card ≤ Lv + H + Lv.divisors.card + ⌈A₀⌉₊ + 1 := by omega
  -- the divisor set `G`
  have hGsub : bigRatioDivisors Lv (H : ℝ) ⊆ Lv.divisors := bigRatioDivisors_subset _ _
  have hGcardN : Lv.divisors.card ≤ 2 * (bigRatioDivisors Lv (H : ℝ)).card :=
    card_divisors_le_two_mul_card_bigRatioDivisors hLvsq hLvpos (by linarith) (by nlinarith)
  have hGcard : (Lv.divisors.card : ℝ) ≤ 2 * ((bigRatioDivisors Lv (H : ℝ)).card : ℝ) := by
    exact_mod_cast hGcardN
  -- the parent primes
  obtain ⟨Bs, hBfresh, hBlow, hBhigh⟩ :=
    exists_freshPrimes_sum_inv_ge_le (Lv + H + Lv.divisors.card + ⌈A₀⌉₊ + 1) (by omega) Ps
      (4 / (Lv.divisors.card : ℝ)) (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hBprime : ∀ q ∈ Bs, q.Prime := fun q hq => (hBfresh q hq).1
  have hBgt : ∀ q ∈ Bs, Lv + H + Lv.divisors.card + ⌈A₀⌉₊ + 1 < q :=
    fun q hq => (hBfresh q hq).2.1
  have hBnotP : ∀ q ∈ Bs, q ∉ Ps := fun q hq => (hBfresh q hq).2.2
  have hBne : Bs.Nonempty := by
    rcases Finset.eq_empty_or_nonempty Bs with h | h
    · exfalso
      rw [h] at hBlow
      rw [Finset.sum_empty] at hBlow
      have : (0 : ℝ) < 4 / (Lv.divisors.card : ℝ) := div_pos (by norm_num) hD0
      linarith
    · exact h
  have hsumBup : (∑ q ∈ Bs, 1 / (q : ℝ)) ≤ 5 / (Lv.divisors.card : ℝ) := by
    refine sum_five_div_aux hD0 ?_ ?_ hBhigh
    · have : (0 : ℕ) < Lv + H + Lv.divisors.card + ⌈A₀⌉₊ + 1 := by omega
      exact_mod_cast this
    · exact_mod_cast hDnat
  -- the tag sets
  obtain ⟨Tg, hTfresh, hTdisj, hTlow, hThigh⟩ :=
    exists_freshPrimes_family H hH0 (fun j : ℕ × ℕ => 4 * (j.2 : ℝ) / (H : ℝ))
      (fun j => div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
      (Bs ×ˢ Lv.divisors) (Ps ∪ Bs)
  -- the selection
  have hpg : ∀ q ∈ Bs, Lv < q := by
    intro q hq
    have := hBgt q hq
    omega
  have htp : ∀ q ∈ Bs, ∀ d ∈ Lv.divisors, ∀ p ∈ Tg (q, d), p.Prime := by
    intro q hq d hd p hp
    exact (hTfresh (q, d) (Finset.mem_product.mpr ⟨hq, hd⟩) p hp).1
  have htne : ∀ q ∈ Bs, ∀ d ∈ Lv.divisors, ∀ p ∈ Tg (q, d), ∀ q' ∈ Bs, p ≠ q' := by
    intro q hq d hd p hp q' hq' heq
    have hnot := (hTfresh (q, d) (Finset.mem_product.mpr ⟨hq, hd⟩) p hp).2.2
    exact hnot (Finset.mem_union_right _ (heq ▸ hq'))
  have htnd : ∀ q ∈ Bs, ∀ d ∈ Lv.divisors, ∀ p ∈ Tg (q, d), ¬ p ∣ Lv := by
    intro q hq d hd p hp hdvd
    have hpp := (hTfresh (q, d) (Finset.mem_product.mpr ⟨hq, hd⟩) p hp).1
    have hnot := (hTfresh (q, d) (Finset.mem_product.mpr ⟨hq, hd⟩) p hp).2.2
    have hcop : Nat.gcd p Lv = 1 := by
      rw [hLvdef]
      exact coprime_primeProd hPprime hpp (fun hc => hnot (Finset.mem_union_left _ hc))
    have h1 : p ∣ Nat.gcd p Lv := Nat.dvd_gcd (dvd_refl p) hdvd
    rw [hcop] at h1
    have h2 := Nat.le_of_dvd Nat.one_pos h1
    have h3 := hpp.one_lt
    omega
  have htd : ∀ q ∈ Bs, ∀ d ∈ Lv.divisors, ∀ q' ∈ Bs, ∀ d' ∈ Lv.divisors,
      ((q, d) : ℕ × ℕ) ≠ (q', d') → Disjoint (Tg (q, d)) (Tg (q', d')) := by
    intro q hq d hd q' hq' d' hd' hne
    exact hTdisj (q, d) (Finset.mem_product.mpr ⟨hq, hd⟩) (q', d')
      (Finset.mem_product.mpr ⟨hq', hd'⟩) hne
  obtain ⟨s, hsH, hsL, hsB, hsT⟩ :
      ∃ s : Selection, s.Hn = H ∧ s.Lv = Lv ∧ s.parents = Bs ∧ s.tagSets = Tg :=
    ⟨⟨H, Lv, Bs, Tg, hH, hLvpos, hLvsq, hBne, hBprime, hpg, htp, htne, htnd, htd⟩,
      rfl, rfl, rfl, rfl⟩
  -- hypotheses in the language of `s`
  have hsupp_parents : ∀ q ∈ s.parents, q ∈ Bs := by rw [hsB]; exact fun q hq => hq
  have hdivs : s.Lv.divisors = Lv.divisors := by rw [hsL]
  have htagup : ∀ q ∈ s.parents, ∀ d ∈ s.Lv.divisors,
      ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ) ≤ 5 * (d : ℝ) / (s.Hn : ℝ) := by
    intro q hq d hd
    rw [hsT, hsH]
    rw [hdivs] at hd
    have hmem : ((q, d) : ℕ × ℕ) ∈ Bs ×ˢ Lv.divisors :=
      Finset.mem_product.mpr ⟨hsupp_parents q hq, hd⟩
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      have := Nat.pos_of_mem_divisors hd
      exact_mod_cast this
    exact tag_sum_upper_aux hHpos hd1 (hThigh (q, d) hmem)
  have hkappa : kappaOne s.support 1 ≤ 30 * Real.log 2 / (H : ℝ) := by
    have h := s.kappaOne_support_le htagup (by rw [hsB, hdivs]; exact hsumBup)
      (by rw [hsH, hdivs]; exact hHD)
    rwa [hsH] at h
  -- the probability clause
  have hmu : ∀ q ∈ s.parents, ∀ r ∈ bigRatioDivisors Lv (H : ℝ),
      4 * (r : ℝ) ≤ ∑ d ∈ s.Lv.divisors.filter (fun d => d ∣ r),
        ∑ p ∈ s.tagSets (q, d), 1 / (p : ℝ) := by
    intro q hq r hr
    obtain ⟨hrdiv, hrsig⟩ := mem_bigRatioDivisors.mp hr
    have hrpos : 0 < r := Nat.pos_of_mem_divisors hrdiv
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
    have hfil : s.Lv.divisors.filter (fun d => d ∣ r) = r.divisors := by
      rw [hdivs]
      exact divisors_filter_dvd hrdiv
    rw [hfil, hsT]
    have hlow : ∀ d ∈ r.divisors, 4 * (d : ℝ) / (H : ℝ) ≤ ∑ p ∈ Tg (q, d), 1 / (p : ℝ) := by
      intro d hd
      have hdL : d ∈ Lv.divisors :=
        Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hd).1.trans (Nat.mem_divisors.mp hrdiv).1,
          hLvpos.ne'⟩
      exact hTlow (q, d) (Finset.mem_product.mpr ⟨hsupp_parents q hq, hdL⟩)
    have hsum1 : (∑ d ∈ r.divisors, 4 * (d : ℝ) / (H : ℝ))
        ≤ ∑ d ∈ r.divisors, ∑ p ∈ Tg (q, d), 1 / (p : ℝ) := Finset.sum_le_sum hlow
    have hsum2 : (∑ d ∈ r.divisors, 4 * (d : ℝ) / (H : ℝ))
        = 4 * ((∑ d ∈ r.divisors, d : ℕ) : ℝ) / (H : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
    have hsig : (H : ℝ) * (r : ℝ) ≤ ((∑ d ∈ r.divisors, d : ℕ) : ℝ) := by
      have hsr : sigmaRatio r = ((∑ d ∈ r.divisors, d : ℕ) : ℝ) / (r : ℝ) := rfl
      rw [hsr, le_div_iff₀ hrR] at hrsig
      linarith
    have := mu_lower_aux hHpos hsig
    linarith
  have hqD : ∀ q ∈ s.parents, (s.Lv.divisors.card : ℝ) ≤ (q : ℝ) := by
    intro q hq
    rw [hdivs]
    have h1 := hBgt q (hsupp_parents q hq)
    have : Lv.divisors.card ≤ q := by omega
    exact_mod_cast this
  have hsumBlow : 4 / (s.Lv.divisors.card : ℝ) ≤ ∑ q ∈ s.parents, 1 / (q : ℝ) := by
    rw [hdivs, hsB]
    exact hBlow
  -- `L ∣ Q`
  obtain ⟨q0, hq0⟩ := hBne
  have hLvmem : Lv ∈ Lv.divisors := Nat.mem_divisors_self _ hLvpos.ne'
  have hTne : (Tg (q0, Lv)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Tg (q0, Lv)) with h | h
    · exfalso
      have hl := hTlow (q0, Lv) (Finset.mem_product.mpr ⟨hq0, hLvmem⟩)
      rw [h, Finset.sum_empty] at hl
      have hLR : (0 : ℝ) < (Lv : ℝ) := by exact_mod_cast hLvpos
      have : (0 : ℝ) < 4 * (Lv : ℝ) / (H : ℝ) := by positivity
      simp only at hl
      linarith
    · exact h
  obtain ⟨p0, hp0⟩ := hTne
  have hq0s : q0 ∈ s.parents := by rw [hsB]; exact hq0
  have hp0s : p0 ∈ s.tagSets (q0, s.Lv) := by rw [hsT, hsL]; exact hp0
  have hLdvd : s.Lv ∣ s.support.lcm id := s.Lv_dvd_lcm hq0s hp0s
  have hprob : 1 - Real.exp (-1) ≤ condExceedProb s.support s.Lv :=
    s.condExceedProb_support_ge (bigRatioDivisors Lv (H : ℝ)) (by rw [hdivs]; exact hGsub)
      (by rw [hdivs]; exact hGcard) hmu hqD hsumBlow hLdvd
  -- clause (iv)
  have hF0 : (0 : ℕ) ∉ s.support := s.zero_notMem_support
  have hLvs : s.Lv = Lv := hsL
  have hP0 : (0 : ℝ) ≤ ((s.support.lcm id / s.Lv : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 / (8 * (((s.support.lcm id / s.Lv : ℕ) : ℝ) + 1)) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hRbound : ((s.support.lcm id / s.Lv : ℕ) : ℝ) / (2 : ℝ) ^ R ≤ 1 / 8 := by
    have hid : (1 / 2 : ℝ) ^ R = 1 / (2 : ℝ) ^ R := by rw [div_pow, one_pow]
    rw [hid] at hR
    have hpow : (0 : ℝ) < (2 : ℝ) ^ R := by positivity
    rw [div_le_div_iff₀ hpow (by norm_num)]
    have h1 : 1 / (2 : ℝ) ^ R < 1 / (8 * (((s.support.lcm id / s.Lv : ℕ) : ℝ) + 1)) := hR
    rw [div_lt_div_iff₀ hpow (by positivity)] at h1
    nlinarith [hP0, hpow]
  have hdy := condExceedProb_sub_le_dyadicMean s.support hF0 s.Lv (by rw [hLvs]; exact hLvpos)
    hLdvd R s.Lv (by rw [hLvs]; exact hLvpos)
  have hexp38 : Real.exp (-1) < 3 / 8 := exp_neg_one_lt_three_eighths
  have hdyR : 1 / 2 < dyadicMean s.Lv R s.Lv (exceedInd s.support) := by linarith
  refine ⟨s.Lv, s.support, ?_, ?_, s.support_nonempty, hF0, ?_, ?_, hLdvd, ?_, hprob, ⟨R, hdyR⟩⟩
  · rw [hLvs]; exact hLvpos
  · rw [hLvs]; exact hLvsq
  · exact fun a ha => ⟨s.pos_of_mem_support ha, s.squarefree_of_mem_support ha⟩
  · intro a ha
    obtain ⟨q, hq, hqa⟩ := s.exists_parent_le_of_mem_support ha
    have hbq := hBgt q (hsupp_parents q hq)
    have hLa : Lv < a := by omega
    have hceil : ⌈A₀⌉₊ < a := by omega
    refine max_lt ?_ ?_
    · rw [hLvs]
      exact_mod_cast hLa
    · have h1 : A₀ ≤ (⌈A₀⌉₊ : ℝ) := Nat.le_ceil A₀
      have h2 : ((⌈A₀⌉₊ : ℕ) : ℝ) < (a : ℝ) := by exact_mod_cast hceil
      linarith
  · exact hkappa

/-- Clause (v) of the long `thm` "arithmetic logarithmic counterexample": no
absolute constant `C` satisfies

  `𝒟_{L;R,M} 1_{U_F > t} ≤ C (1 + L/M) κ₁(F;t)`

uniformly in finite `F`, positive integers `L, M`, integers `R ≥ 0` and
`0 < t ≤ 1`. -/
theorem no_absolute_dyadic_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ (F : Finset ℕ), F.Nonempty → (0 : ℕ) ∉ F →
      ∀ (L M : ℕ), 0 < L → 0 < M → ∀ (R : ℕ) (t : ℝ), 0 < t → t ≤ 1 →
        dyadicMean L R M (fun N => if t < framePotential F N then (1 : ℝ) else 0)
          ≤ C * (1 + (L : ℝ) / (M : ℝ)) * kappaOne F t := by
  rintro ⟨C, hC⟩
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCle : C ≤ Cp := le_max_left _ _
  obtain ⟨H, hH2, hHbig⟩ : ∃ H : ℕ, 2 ≤ H ∧ 120 * Cp * Real.log 2 < (H : ℝ) := by
    refine ⟨⌈120 * Cp * Real.log 2⌉₊ + 2, by omega, ?_⟩
    have h1 : 120 * Cp * Real.log 2 ≤ (⌈120 * Cp * Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  obtain ⟨L, F, hL0, -, hFne, hF0, -, -, -, hkappa, -, R, hdy⟩ :=
    arithmetic_logarithmic_counterexample H hH2 0 le_rfl
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  have hbound := hC F hFne hF0 L L hL0 hL0 R 1 one_pos le_rfl
  have hfun : (fun N => if (1 : ℝ) < framePotential F N then (1 : ℝ) else 0) = exceedInd F := rfl
  rw [hfun] at hbound
  have hLL : (L : ℝ) / (L : ℝ) = 1 := div_self (ne_of_gt hLR)
  rw [hLL] at hbound
  have hk0 : 0 ≤ kappaOne F 1 := kappaOne_nonneg F
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    have : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH2
    linarith
  have hstep1 : C * (1 + 1) * kappaOne F 1 ≤ Cp * (1 + 1) * kappaOne F 1 := by
    nlinarith [hk0, hCle]
  have hstep2 : Cp * (1 + 1) * kappaOne F 1 ≤ Cp * (1 + 1) * (30 * Real.log 2 / (H : ℝ)) := by
    nlinarith [hCp0, hkappa]
  have hstep3 : Cp * (1 + 1) * (30 * Real.log 2 / (H : ℝ)) < 1 / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ hHpos (by norm_num)]
    nlinarith [hHbig]
  linarith

/-! ### The corollary -/

/-- Long `cor` "finite-functional separation"
(`paper/reasoning-parts/erdos257/a257_front.tex:9369`), clauses 2 and 3: the
supports of the theorem satisfy `K_*(F) ≥ 1 - e^{-1}` and
`κ₁(F;1) ≤ 30 log 2 / H`, so no absolute `C` gives `K_*(F) ≤ C κ₁(F;1)`. -/
theorem exists_support_paperCoverCost_ge (H : ℕ) (hH : 2 ≤ H) :
    ∃ F : Finset ℕ, F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      1 - Real.exp (-1) ≤ paperCoverCost (F : Set ℕ) ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) := by
  obtain ⟨L, F, hL0, -, hFne, hF0, -, -, hLdvd, hkappa, hprob, -⟩ :=
    arithmetic_logarithmic_counterexample H hH 0 le_rfl
  exact ⟨F, hFne, hF0,
    le_trans hprob (condExceedProb_le_paperCoverCost F hF0 L hL0 hLdvd), hkappa⟩

/-- Clause 3 of the corollary: "no absolute `C` gives `K_*(F) ≤ C κ₁(F;1)` for
all finite nonempty `F`, even after all covering sets, exponents, coefficients
and positive weights have been optimised." -/
theorem no_absolute_paperCoverCost_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ F : Finset ℕ, F.Nonempty → (0 : ℕ) ∉ F →
      paperCoverCost (F : Set ℕ) ≤ C * kappaOne F 1 := by
  rintro ⟨C, hC⟩
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCle : C ≤ Cp := le_max_left _ _
  obtain ⟨H, hH2, hHbig⟩ : ∃ H : ℕ, 2 ≤ H ∧ 48 * Cp * Real.log 2 < (H : ℝ) := by
    refine ⟨⌈48 * Cp * Real.log 2⌉₊ + 2, by omega, ?_⟩
    have h1 : 48 * Cp * Real.log 2 ≤ (⌈48 * Cp * Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  obtain ⟨F, hFne, hF0, hK, hkappa⟩ := exists_support_paperCoverCost_ge H hH2
  have hHpos : (0 : ℝ) < (H : ℝ) := by
    have : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH2
    linarith
  have hk0 : 0 ≤ kappaOne F 1 := kappaOne_nonneg F
  have hbound := hC F hFne hF0
  have hstep1 : C * kappaOne F 1 ≤ Cp * kappaOne F 1 := by nlinarith [hk0, hCle]
  have hstep2 : Cp * kappaOne F 1 ≤ Cp * (30 * Real.log 2 / (H : ℝ)) := by
    nlinarith [hCp0, hkappa]
  have hstep3 : Cp * (30 * Real.log 2 / (H : ℝ)) < 5 / 8 := by
    rw [mul_div_assoc', div_lt_div_iff₀ hHpos (by norm_num)]
    nlinarith [hHbig]
  have hexp38 : Real.exp (-1) < 3 / 8 := exp_neg_one_lt_three_eighths
  linarith

#print axioms prod_dvd_of_pairwise_coprime
#print axioms card_filter_mod_mem_mul
#print axioms card_filter_forall_mod_mem_prod
#print axioms card_filter_forall_mod_mem
#print axioms half_card_le_card_filter_le
#print axioms TagFamily.crt_count
#print axioms TagFamily.tagCount_eq_condTags
#print axioms TagFamily.period_div_two_parent_le_card_succSet
#print axioms TagFamily.card_parentSuccess_ge
#print axioms TagFamily.success_mod_period
#print axioms Selection.kappaOne_support_le
#print axioms Selection.condExceedProb_support_ge
#print axioms arithmetic_logarithmic_counterexample
#print axioms no_absolute_dyadic_kappaOne_constant
#print axioms exists_support_paperCoverCost_ge
#print axioms no_absolute_paperCoverCost_kappaOne_constant
-- Clause 1 of the corollary, proved in `ArithmeticCoverLowerBoundPaperForm.lean`:
#print axioms sup_condExceedProb_le_paperCoverCost

end ErdosProblems.Erdos257.PaperCompleteR21

end
