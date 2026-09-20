import ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval

/-!
# Prime and divisor selection for the arithmetic logarithmic counterexample

The first half of the construction inside the long Erdős #257 `thm`
"arithmetic logarithmic counterexample"
(`paper/reasoning-parts/erdos257/a257_front.tex:9212`).

The theorem's proof opens by choosing

* a finite set of primes `P` with `B = ∏_{p ∈ P}(1 + 1/p) ≥ H²`, possible
  "because the sum of reciprocal primes diverges and `log(1 + 1/p) ≥ 1/(2p)`";
* a finite set `𝓑` of parent primes, all above a cutoff, with
  `4/D ≤ ∑_{q ∈ 𝓑} 1/q ≤ 5/D`, by "stopping at the first crossing of `4/D`;
  the overshoot is less than `1/D`";
* for each `q ∈ 𝓑` and `d ∣ L` a finite set `T_{q,d}` of tag primes, all
  greater than `H` and disjoint from everything chosen so far, with
  `4d/H ≤ S_{q,d} ≤ 5d/H`, by "the same stopping argument ... only finitely
  many primes have been excluded";

and then uses, with `L = ∏_{p ∈ P} p`, `D = τ(L)`,

* the complementary-divisor identity
  `(σ(r)/r)(σ(L/r)/(L/r)) = B` for `r ∣ L`;
* "thus the set `G = {r ∣ L : σ(r)/r ≥ H}` has at least `D/2` elements";
* "also `D ≥ B ≥ H²`".

This module proves exactly those selection and divisor facts.  Each is stated
for arbitrary parameters, so the two prime selections of the paper are the same
lemma `exists_freshPrimes_sum_inv_ge_le` used twice: once with target `4/D` and
cutoff above `D`, once with target `4d/H` and cutoff `H`.

What is *not* here, and remains for the theorem: the least-common-multiple
encoding `f_{F_q}(n) = 1_{q ∣ n} 2^{Z_q(n)}`, the logarithmic majorant cost
`(log 2 / q)(1 + 5D/H)`, and the conditional Chebyshev and independence
estimates that give `ℙ_L(U_F > 1) ≥ 1 - e^{-1}`.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset

/-! ### The paper's `log(1 + x) ≥ x/2` -/

/-- `exp(x/2) ≤ 1 + x` on `[0, 1]`: from `1 - x/2 ≤ exp(-x/2)` and
`1 ≤ (1 + x)(1 - x/2)`. -/
theorem exp_half_le_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (x / 2) ≤ 1 + x := by
  have hden : (0 : ℝ) < 1 - x / 2 := by linarith
  have hexp : (1 : ℝ) - x / 2 ≤ Real.exp (-(x / 2)) := by
    have h := Real.add_one_le_exp (-(x / 2))
    linarith
  have hpos : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have hmul : Real.exp (x / 2) * (1 - x / 2) ≤ Real.exp (x / 2) * Real.exp (-(x / 2)) :=
    mul_le_mul_of_nonneg_left hexp hpos.le
  have hone : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hone] at hmul
  have hother : (1 : ℝ) ≤ (1 + x) * (1 - x / 2) := by nlinarith
  have hfin : Real.exp (x / 2) * (1 - x / 2) ≤ (1 + x) * (1 - x / 2) :=
    le_trans hmul hother
  exact le_of_mul_le_mul_right hfin hden

/-- The paper's `log(1 + 1/p) ≥ 1/(2p)`, in the general form `log(1 + x) ≥ x/2`
for `0 ≤ x ≤ 1`. -/
theorem half_le_log_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have h := exp_half_le_one_add hx0 hx1
  have h2 := Real.log_le_log (Real.exp_pos (x / 2)) h
  rwa [Real.log_exp] at h2

/-! ### Fresh primes -/

/-- The paper's admissibility condition for each successive prime selection: a
prime above a cutoff `b` and outside the finite set `E` of primes already
used. -/
def FreshPrime (b : ℕ) (E : Finset ℕ) (n : ℕ) : Prop := n.Prime ∧ b < n ∧ n ∉ E

instance decidableFreshPrime (b : ℕ) (E : Finset ℕ) (n : ℕ) :
    Decidable (FreshPrime b E n) :=
  inferInstanceAs (Decidable (n.Prime ∧ b < n ∧ n ∉ E))

/-- "Divergence of the prime reciprocal sum after any finite cutoff": excluding
an initial segment and a finite set leaves a divergent reciprocal sum. -/
theorem not_summable_freshPrime_inv (b : ℕ) (E : Finset ℕ) :
    ¬ Summable (fun n : ℕ => if FreshPrime b E n then (1 : ℝ) / n else 0) := by
  intro hsum
  have hind : ∀ n : ℕ,
      Set.indicator {p : ℕ | p.Prime} (fun m : ℕ => (1 : ℝ) / m) n
        = if n.Prime then (1 : ℝ) / n else 0 := by
    intro n
    by_cases hp : n.Prime <;> simp [Set.indicator_apply, hp]
  have hdiff : Summable (fun n : ℕ =>
      (if n.Prime then (1 : ℝ) / n else 0)
        - (if FreshPrime b E n then (1 : ℝ) / n else 0)) := by
    refine summable_of_ne_finset_zero (s := Finset.range (b + 1) ∪ E) ?_
    intro n hn
    simp only [Finset.mem_union, Finset.mem_range, not_or, not_lt] at hn
    obtain ⟨hnb, hnE⟩ := hn
    by_cases hp : n.Prime
    · have hfresh : FreshPrime b E n := ⟨hp, by omega, hnE⟩
      rw [if_pos hp, if_pos hfresh, sub_self]
    · have hnot : ¬ FreshPrime b E n := fun h => hp h.1
      rw [if_neg hp, if_neg hnot, sub_self]
  have hfull : Summable (Set.indicator {p : ℕ | p.Prime} (fun m : ℕ => (1 : ℝ) / m)) := by
    have h := hdiff.add hsum
    refine h.congr ?_
    intro n
    rw [hind n]
    ring
  exact not_summable_one_div_on_primes hfull

/-- The paper's stopping argument, in the form both of its prime selections
use: for every target `a ≥ 0`, every cutoff `b ≥ 1` and every finite set `E` of
primes already used, there is a finite set `S` of primes, all greater than `b`
and none in `E`, whose reciprocal sum first crosses `a`, so that

  `a ≤ ∑_{p ∈ S} 1/p ≤ a + 1/b`,

"the overshoot" being at most the reciprocal of the cutoff. -/
theorem exists_freshPrimes_sum_inv_ge_le (b : ℕ) (hb : 0 < b) (E : Finset ℕ)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ b < p ∧ p ∉ E) ∧
      a ≤ ∑ p ∈ S, (1 : ℝ) / p ∧ ∑ p ∈ S, (1 : ℝ) / p ≤ a + 1 / b := by
  classical
  set f : ℕ → ℝ := fun n => if FreshPrime b E n then (1 : ℝ) / n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    simp only [hf]
    split_ifs with h
    · positivity
    · exact le_rfl
  have hpart : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, f n)
        = ∑ p ∈ (Finset.range N).filter (fun n => FreshPrime b E n), (1 : ℝ) / p := by
    intro N
    rw [Finset.sum_filter]
  have hcross : ∃ N : ℕ, a ≤ ∑ n ∈ Finset.range N, f n := by
    by_contra hcon
    push_neg at hcon
    exact not_summable_freshPrime_inv b E
      (summable_of_sum_range_le hf0 (fun n => (hcon n).le))
  classical
  set N := Nat.find hcross with hN
  have hNspec : a ≤ ∑ n ∈ Finset.range N, f n := Nat.find_spec hcross
  refine ⟨(Finset.range N).filter (fun n => FreshPrime b E n), ?_, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · rw [← hpart]
    exact hNspec
  · rw [← hpart]
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · have hzero : (∑ n ∈ Finset.range N, f n) = 0 := by rw [hN0]; simp
      have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
      rw [hzero]
      linarith
    · obtain ⟨k, hk⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
      have hprev : ¬ (a ≤ ∑ n ∈ Finset.range k, f n) := by
        have := Nat.find_min hcross (m := k) (by omega)
        exact this
      push_neg at hprev
      have hstep : (∑ n ∈ Finset.range N, f n)
          = (∑ n ∈ Finset.range k, f n) + f k := by
        rw [hk, Finset.sum_range_succ]
      have hfk : f k ≤ 1 / (b : ℝ) := by
        simp only [hf]
        split_ifs with hfresh
        · have hkb : b < k := hfresh.2.1
          have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
          have hkR : (b : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkb.le
          exact one_div_le_one_div_of_le hbR hkR
        · have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
          positivity
      rw [hstep]
      linarith

/-- "The same stopping argument works successively: each new reciprocal is less
than `1/H ≤ d/H`, and only finitely many primes have been excluded."  The whole
family of tag sets `T_{q,d}` at once: pairwise disjoint finite sets of primes,
all above the cutoff and outside the finite set already used, each meeting its
own target with overshoot at most `1/b`. -/
theorem exists_freshPrimes_family {ι : Type*} [DecidableEq ι] (b : ℕ) (hb : 0 < b)
    (target : ι → ℝ) (htarget : ∀ j, 0 ≤ target j) (J : Finset ι) :
    ∀ E : Finset ℕ, ∃ S : ι → Finset ℕ,
      (∀ j ∈ J, ∀ p ∈ S j, p.Prime ∧ b < p ∧ p ∉ E) ∧
      (∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → Disjoint (S j) (S j')) ∧
      (∀ j ∈ J, target j ≤ ∑ p ∈ S j, (1 : ℝ) / p) ∧
      (∀ j ∈ J, ∑ p ∈ S j, (1 : ℝ) / p ≤ target j + 1 / b) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      intro E
      exact ⟨fun _ => ∅, by simp, by simp, by simp, by simp⟩
  | insert a J' ha ih =>
      intro E
      obtain ⟨Sa, hSa, hlowa, hhigha⟩ :=
        exists_freshPrimes_sum_inv_ge_le b hb E (target a) (htarget a)
      obtain ⟨S', hfresh', hdisj', hlow', hhigh'⟩ := ih (E ∪ Sa)
      refine ⟨fun j => if j = a then Sa else S' j, ?_, ?_, ?_, ?_⟩
      · intro j hj p hp
        dsimp only at hp
        by_cases hja : j = a
        · rw [if_pos hja] at hp
          exact hSa p hp
        · rw [if_neg hja] at hp
          have hjJ' : j ∈ J' := by
            rcases Finset.mem_insert.mp hj with h | h
            · exact absurd h hja
            · exact h
          obtain ⟨hpp, hpb, hpE⟩ := hfresh' j hjJ' p hp
          exact ⟨hpp, hpb, fun hc => hpE (Finset.mem_union_left _ hc)⟩
      · intro j hj j' hj' hne
        dsimp only
        have hnotSa : ∀ k ∈ J', Disjoint Sa (S' k) := by
          intro k hk
          rw [Finset.disjoint_left]
          intro p hpSa hpS'
          exact (hfresh' k hk p hpS').2.2 (Finset.mem_union_right _ hpSa)
        by_cases hja : j = a
        · have hj'J' : j' ∈ J' := by
            rcases Finset.mem_insert.mp hj' with h | h
            · exact absurd (hja ▸ h.symm) hne
            · exact h
          have hj'a : j' ≠ a := fun h => ha (h ▸ hj'J')
          rw [if_pos hja, if_neg hj'a]
          exact hnotSa j' hj'J'
        · have hjJ' : j ∈ J' := by
            rcases Finset.mem_insert.mp hj with h | h
            · exact absurd h hja
            · exact h
          by_cases hj'a : j' = a
          · rw [if_neg hja, if_pos hj'a]
            exact (hnotSa j hjJ').symm
          · have hj'J' : j' ∈ J' := by
              rcases Finset.mem_insert.mp hj' with h | h
              · exact absurd h hj'a
              · exact h
            rw [if_neg hja, if_neg hj'a]
            exact hdisj' j hjJ' j' hj'J' hne
      · intro j hj
        dsimp only
        by_cases hja : j = a
        · rw [if_pos hja, hja]
          exact hlowa
        · have hjJ' : j ∈ J' := by
            rcases Finset.mem_insert.mp hj with h | h
            · exact absurd h hja
            · exact h
          rw [if_neg hja]
          exact hlow' j hjJ'
      · intro j hj
        dsimp only
        by_cases hja : j = a
        · rw [if_pos hja, hja]
          exact hhigha
        · have hjJ' : j ∈ J' := by
            rcases Finset.mem_insert.mp hj with h | h
            · exact absurd h hja
            · exact h
          rw [if_neg hja]
          exact hhigh' j hjJ'

/-- The paper's first selection: a finite set of primes, above any cutoff and
avoiding any finite set already used, with `∏ (1 + 1/p)` at least any target.
"Such a set exists because the sum of reciprocal primes diverges and
`log(1 + 1/p) ≥ 1/(2p)`." -/
theorem exists_freshPrimes_prod_one_add_inv_ge (b : ℕ) (hb : 0 < b) (E : Finset ℕ)
    (Y : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ b < p ∧ p ∉ E) ∧
      Y ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
  classical
  obtain ⟨S, hS, hlow, -⟩ :=
    exists_freshPrimes_sum_inv_ge_le b hb E (max 0 (2 * Real.log Y)) (le_max_left _ _)
  refine ⟨S, hS, ?_⟩
  have hfactor : ∀ p ∈ S, Real.exp ((1 / (p : ℝ)) / 2) ≤ 1 + 1 / (p : ℝ) := by
    intro p hp
    obtain ⟨hpp, -, -⟩ := hS p hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    refine exp_half_le_one_add (by positivity) ?_
    rw [div_le_one hp0]
    exact hp1
  have hprod : Real.exp (∑ p ∈ S, (1 / (p : ℝ)) / 2) ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) hfactor
  have hsumhalf : (∑ p ∈ S, (1 / (p : ℝ)) / 2) = (∑ p ∈ S, (1 : ℝ) / p) / 2 := by
    rw [Finset.sum_div]
  rcases le_or_gt Y 1 with hY | hY
  · have hterm : ∀ p ∈ S, (1 : ℝ) ≤ 1 + 1 / (p : ℝ) := by
      intro p hp
      obtain ⟨hpp, -, -⟩ := hS p hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
      have hinv : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith
    have hone : (1 : ℝ) ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
      have h := Finset.prod_le_prod (s := S) (f := fun _ : ℕ => (1 : ℝ))
        (g := fun p : ℕ => 1 + 1 / (p : ℝ)) (fun p _ => zero_le_one) hterm
      simpa using h
    linarith
  · have hYpos : (0 : ℝ) < Y := by linarith
    have hlogpos : 0 < Real.log Y := Real.log_pos hY
    have hmax : max 0 (2 * Real.log Y) = 2 * Real.log Y := by
      apply max_eq_right
      linarith
    rw [hmax] at hlow
    have hhalf : Real.log Y ≤ (∑ p ∈ S, (1 : ℝ) / p) / 2 := by linarith
    have hstep : Y ≤ Real.exp ((∑ p ∈ S, (1 : ℝ) / p) / 2) := by
      calc Y = Real.exp (Real.log Y) := (Real.exp_log hYpos).symm
        _ ≤ Real.exp ((∑ p ∈ S, (1 : ℝ) / p) / 2) := Real.exp_le_exp.mpr hhalf
    rw [hsumhalf] at hprod
    linarith

/-! ### The divisor ratio `σ(n)/n` -/

/-- The paper's `σ(n)/n`, where `σ` is the sum of positive divisors. -/
def sigmaRatio (n : ℕ) : ℝ := ((∑ d ∈ n.divisors, d : ℕ) : ℝ) / (n : ℝ)

theorem one_le_sigmaRatio {n : ℕ} (hn : 0 < n) : 1 ≤ sigmaRatio n := by
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hle : n ≤ ∑ d ∈ n.divisors, d :=
    Finset.single_le_sum (f := fun d : ℕ => d) (fun d _ => Nat.zero_le d) hmem
  have hleR : (n : ℝ) ≤ ((∑ d ∈ n.divisors, d : ℕ) : ℝ) := by exact_mod_cast hle
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [sigmaRatio, le_div_iff₀ hnR, one_mul]
  exact hleR

theorem sigmaRatio_pos {n : ℕ} (hn : 0 < n) : 0 < sigmaRatio n :=
  lt_of_lt_of_le zero_lt_one (one_le_sigmaRatio hn)

/-- `σ(n)/n` is multiplicative on coprime arguments. -/
theorem sigmaRatio_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    sigmaRatio (m * n) = sigmaRatio m * sigmaRatio n := by
  have hsum : (∑ d ∈ (m * n).divisors, d)
      = (∑ d ∈ m.divisors, d) * (∑ d ∈ n.divisors, d) := h.sum_divisors_mul
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold sigmaRatio
  rw [hsum]
  push_cast
  field_simp

/-- The paper's `σ(r)/r · σ(L/r)/(L/r) = B` for `r ∣ L` and `L` squarefree. -/
theorem sigmaRatio_mul_complement {L r : ℕ} (hL : Squarefree L) (hL0 : 0 < L)
    (hr : r ∣ L) :
    sigmaRatio r * sigmaRatio (L / r) = sigmaRatio L := by
  have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hr hL0
  set s : ℕ := L / r with hs
  have hmul : r * s = L := Nat.mul_div_cancel' hr
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · exfalso; rw [h0, Nat.mul_zero] at hmul; omega
    · exact hpos
  have hcop : Nat.Coprime r s := by
    have h1 : Nat.gcd r s ∣ r := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd r s ∣ s := Nat.gcd_dvd_right _ _
    have hdvd : Nat.gcd r s * Nat.gcd r s ∣ L := by
      have := mul_dvd_mul h1 h2
      rwa [hmul] at this
    exact Nat.isUnit_iff.mp (hL _ hdvd)
  rw [← sigmaRatio_mul hrpos hspos hcop, hmul]

/-! ### Squarefree products of primes -/

/-- The paper's `L = ∏_{p ∈ P} p`. -/
def primeProd (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

theorem primeProd_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) : 0 < primeProd P :=
  Finset.prod_pos fun p hp => (hP p hp).pos

theorem coprime_primeProd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {p : ℕ} (hp : p.Prime) (hnot : p ∉ P) : Nat.Coprime p (primeProd P) :=
  Nat.Coprime.prod_right fun q hq =>
    (Nat.coprime_primes hp (hP q hq)).mpr (fun h => hnot (by rw [h]; exact hq))

theorem primeProd_squarefree {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (primeProd P) := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _; simp [primeProd]
  | insert a s ha ih =>
      intro hP
      have haP : a.Prime := hP a (Finset.mem_insert_self a s)
      have hsP : ∀ p ∈ s, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
      have hprod : primeProd (insert a s) = a * primeProd s := by
        unfold primeProd
        rw [Finset.prod_insert ha]
      rw [hprod, Nat.squarefree_mul_iff]
      exact ⟨coprime_primeProd hsP haP ha, haP.squarefree, ih hsP⟩

theorem sigmaRatio_prime {p : ℕ} (hp : p.Prime) :
    sigmaRatio p = 1 + 1 / (p : ℝ) := by
  have hdiv : p.divisors = {1, p} := hp.divisors
  have hne : (1 : ℕ) ≠ p := fun h => by
    have := hp.one_lt
    omega
  have hsum : (∑ d ∈ p.divisors, d) = 1 + p := by
    rw [hdiv, Finset.sum_pair hne]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  unfold sigmaRatio
  rw [hsum]
  push_cast
  field_simp
  ring

/-- The paper's `B = ∏_{p ∈ P}(1 + 1/p)` is `σ(L)/L`. -/
theorem sigmaRatio_primeProd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    sigmaRatio (primeProd P) = ∏ p ∈ P, (1 + 1 / (p : ℝ)) := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _; simp [primeProd, sigmaRatio]
  | insert a s ha ih =>
      intro hP
      have haP : a.Prime := hP a (Finset.mem_insert_self a s)
      have hsP : ∀ p ∈ s, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
      have hprod : primeProd (insert a s) = a * primeProd s := by
        unfold primeProd
        rw [Finset.prod_insert ha]
      rw [hprod, sigmaRatio_mul haP.pos (primeProd_pos hsP)
        (coprime_primeProd hsP haP ha), sigmaRatio_prime haP, ih hsP,
        Finset.prod_insert ha]

/-- The paper's `D = τ(L) = 2^{|P|}`. -/
theorem card_divisors_primeProd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    (primeProd P).divisors.card = 2 ^ P.card := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _; simp [primeProd]
  | insert a s ha ih =>
      intro hP
      have haP : a.Prime := hP a (Finset.mem_insert_self a s)
      have hsP : ∀ p ∈ s, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
      have hprod : primeProd (insert a s) = a * primeProd s := by
        unfold primeProd
        rw [Finset.prod_insert ha]
      have hne : (1 : ℕ) ≠ a := fun h => by
        have := haP.one_lt
        omega
      have hcarda : a.divisors.card = 2 := by
        rw [haP.divisors, Finset.card_insert_of_notMem (by simpa using hne)]
        simp
      rw [hprod, Nat.Coprime.card_divisors_mul (coprime_primeProd hsP haP ha),
        hcarda, ih hsP, Finset.card_insert_of_notMem ha]
      ring

/-- The paper's "also `D ≥ B`". -/
theorem sigmaRatio_primeProd_le_card_divisors {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    sigmaRatio (primeProd P) ≤ ((primeProd P).divisors.card : ℝ) := by
  classical
  rw [sigmaRatio_primeProd hP, card_divisors_primeProd hP]
  have hle : ∏ p ∈ P, (1 + 1 / (p : ℝ)) ≤ ∏ _p ∈ P, (2 : ℝ) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).one_lt.le
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith
    · intro p hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).one_lt.le
      have hinv : 1 / (p : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hp1
      linarith
  have hconst : ∏ _p ∈ P, (2 : ℝ) = (2 : ℝ) ^ P.card := by
    rw [Finset.prod_const]
  have hcast : ((2 ^ P.card : ℕ) : ℝ) = (2 : ℝ) ^ P.card := by push_cast; ring
  rw [hcast]
  rw [hconst] at hle
  exact hle

/-! ### The paper's `G = {r ∣ L : σ(r)/r ≥ H}` -/

open scoped Classical in
/-- The paper's `G = {r ∣ L : σ(r)/r ≥ H}`. -/
def bigRatioDivisors (L : ℕ) (Hr : ℝ) : Finset ℕ :=
  L.divisors.filter (fun r => Hr ≤ sigmaRatio r)

theorem mem_bigRatioDivisors {L : ℕ} {Hr : ℝ} {r : ℕ} :
    r ∈ bigRatioDivisors L Hr ↔ r ∈ L.divisors ∧ Hr ≤ sigmaRatio r := by
  classical
  unfold bigRatioDivisors
  exact Finset.mem_filter

theorem bigRatioDivisors_subset (L : ℕ) (Hr : ℝ) :
    bigRatioDivisors L Hr ⊆ L.divisors := by
  intro r hr
  exact (mem_bigRatioDivisors.mp hr).1

/-- The paper's "thus the set `G = {r ∣ L : σ(r)/r ≥ H}` has at least `D/2`
elements", given `B = σ(L)/L ≥ H²`.  The complementary divisor `L/r` of a
divisor outside `G` lies in `G`, and `r ↦ L/r` is injective on divisors. -/
theorem card_divisors_le_two_mul_card_bigRatioDivisors {L : ℕ} (hL : Squarefree L)
    (hL0 : 0 < L) {Hr : ℝ} (hHr : 0 < Hr) (hB : Hr * Hr ≤ sigmaRatio L) :
    L.divisors.card ≤ 2 * (bigRatioDivisors L Hr).card := by
  classical
  set G := bigRatioDivisors L Hr with hG
  have hsub : G ⊆ L.divisors := bigRatioDivisors_subset L Hr
  have hcard : (L.divisors \ G).card + G.card = L.divisors.card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hinj : (L.divisors \ G).card ≤ G.card := by
    refine Finset.card_le_card_of_injOn (fun r => L / r) ?_ ?_
    · intro r hr
      obtain ⟨hrdiv, hrnot⟩ := Finset.mem_sdiff.mp hr
      have hrdvd : r ∣ L := (Nat.mem_divisors.mp hrdiv).1
      have hrpos : 0 < r := Nat.pos_of_mem_divisors hrdiv
      have hsmall : sigmaRatio r < Hr := by
        by_contra hcon
        push_neg at hcon
        exact hrnot (mem_bigRatioDivisors.mpr ⟨hrdiv, hcon⟩)
      have hspos : 0 < L / r := Nat.div_pos (Nat.le_of_dvd hL0 hrdvd) hrpos
      have hprod := sigmaRatio_mul_complement hL hL0 hrdvd
      have hrp : 0 < sigmaRatio r := sigmaRatio_pos hrpos
      have hsp : 0 < sigmaRatio (L / r) := sigmaRatio_pos hspos
      have hbig : Hr ≤ sigmaRatio (L / r) := by
        by_contra hcon
        push_neg at hcon
        nlinarith
      refine mem_bigRatioDivisors.mpr ⟨?_, hbig⟩
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hrdvd, hL0.ne'⟩
    · intro r1 h1 r2 h2 heq
      have hd1 : r1 ∣ L :=
        (Nat.mem_divisors.mp (Finset.mem_sdiff.mp (Finset.mem_coe.mp h1)).1).1
      have hd2 : r2 ∣ L :=
        (Nat.mem_divisors.mp (Finset.mem_sdiff.mp (Finset.mem_coe.mp h2)).1).1
      have e1 : L / (L / r1) = r1 := Nat.div_div_self hd1 hL0.ne'
      have e2 : L / (L / r2) = r2 := Nat.div_div_self hd2 hL0.ne'
      simp only at heq
      rw [← e1, ← e2, heq]
  omega

#print axioms half_le_log_one_add
#print axioms exists_freshPrimes_sum_inv_ge_le
#print axioms exists_freshPrimes_family
#print axioms exists_freshPrimes_prod_one_add_inv_ge
#print axioms sigmaRatio_mul_complement
#print axioms sigmaRatio_primeProd
#print axioms card_divisors_primeProd
#print axioms sigmaRatio_primeProd_le_card_divisors
#print axioms card_divisors_le_two_mul_card_bigRatioDivisors

end ErdosProblems.Erdos257.PaperCompleteR21

end
