import ErdosProblems.Erdos257.PaperCompleteR21.LogarithmicInitialInterval

/-!
# The least-common-multiple encoding of one parent group (long #257, line 9212)

The combinatorial heart of the long Erdős #257 `thm` "arithmetic logarithmic
counterexample" (`paper/reasoning-parts/erdos257/a257_front.tex:9212`).  For one
parent prime `q` the paper sets
`𝓘_q = {(d, p) : d ∣ L, p ∈ T_{q,d}}` and

  `F_q = { q · lcm{ d p : (d,p) ∈ I } : I ⊆ 𝓘_q }`,
  `Z_q(n) = ∑_{(d,p) ∈ 𝓘_q} 1_{d p ∣ n}`,

and asserts the exact identity

  `f_{F_q}(n) = 1_{q ∣ n} · 2^{Z_q(n)}`     (`incidenceCount_parentFrame`)

together with its logarithmic consequence

  `log(1 + f_{F_q}(n)) ≤ (log 2)(1_{q ∣ n} + ∑_{(d,p) ∈ 𝓘_q} 1_{q d p ∣ n})`
                                            (`log_one_add_incidenceCount_le`),

"all moduli in this majorant divide `lcm(F_q)`", whose cost is at most
`(log 2 / q)(1 + ∑_{d ∣ L} S_{q,d}/d)`   (`parentMajorantCost_eq`).

The paper's argument for the identity is "every tag prime occurs in just one
labelled pair; its presence in the least common multiple therefore recovers
whether that pair was selected", and "when `q ∣ n`, a selected least common
multiple divides `n` exactly when every selected pair does".

`ParentTagData` below is exactly that data, with the paper's separation
properties as fields: each labelled pair `i` carries its modulus `w i = d p` and
its tag prime `tag i = p`, the tag prime divides its own modulus and no other
one and not the parent, and the parent is coprime to every modulus.  Nothing
here uses that `w i` factors as `d · p`; only the separation matters, which is
why the statements are about an abstract labelled family.

This module is one layer of `thm:257-logarithmic-counterexample`.  The prime
and divisor selections that produce the data are in
`ArithmeticCounterexampleSelection.lean`; the conditional Chebyshev and
independence estimates behind `ℙ_L(U_F > 1) ≥ 1 - e^{-1}` are not formalised.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset

/-- The paper's labelled-pair data `𝓘_q` for one parent prime `q`: a finite
index set of pairs, each carrying its modulus `d p` and its tag prime `p`, with
the separation properties the construction arranges — "every tag prime occurs in
just one labelled pair", the tag sets are disjoint from `𝓑` and from `P`, and
the parent primes exceed `L`. -/
structure ParentTagData where
  /-- The parent prime `q`. -/
  parent : ℕ
  /-- The index set `𝓘_q` of labelled pairs. -/
  idx : Finset ℕ
  /-- The modulus `d p` of a labelled pair. -/
  modulus : ℕ → ℕ
  /-- The tag prime `p` of a labelled pair. -/
  tag : ℕ → ℕ
  parent_prime : parent.Prime
  tag_prime : ∀ i ∈ idx, (tag i).Prime
  tag_dvd_modulus : ∀ i ∈ idx, tag i ∣ modulus i
  modulus_pos : ∀ i ∈ idx, 0 < modulus i
  tag_not_dvd_parent : ∀ i ∈ idx, ¬ tag i ∣ parent
  tag_not_dvd_other : ∀ i ∈ idx, ∀ j ∈ idx, i ≠ j → ¬ tag i ∣ modulus j
  parent_coprime_modulus : ∀ i ∈ idx, Nat.Coprime parent (modulus i)

namespace ParentTagData

variable (P : ParentTagData)

/-- The paper's `F_q = { q · lcm{ d p : (d,p) ∈ I } : I ⊆ 𝓘_q }`, with the least
common multiple of the empty set equal to one. -/
def frame : Finset ℕ := P.idx.powerset.image (fun I => P.parent * I.lcm P.modulus)

/-- The paper's `Z_q(n) = ∑_{(d,p) ∈ 𝓘_q} 1_{d p ∣ n}`. -/
def tagCount (n : ℕ) : ℕ := (P.idx.filter (fun i => P.modulus i ∣ n)).card

theorem coprime_parent_lcm {I : Finset ℕ} (hI : I ⊆ P.idx) :
    Nat.Coprime P.parent (I.lcm P.modulus) := by
  have hprod : Nat.Coprime P.parent (∏ i ∈ I, P.modulus i) :=
    Nat.Coprime.prod_right fun i hi => P.parent_coprime_modulus i (hI hi)
  have hlcm : I.lcm P.modulus ∣ ∏ i ∈ I, P.modulus i :=
    Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi
  exact Nat.Coprime.coprime_dvd_right hlcm hprod

/-- The paper's "when `q ∣ n`, a selected least common multiple divides `n`
exactly when every selected pair does". -/
theorem mem_dvd_iff {I : Finset ℕ} (hI : I ⊆ P.idx) (n : ℕ) :
    P.parent * I.lcm P.modulus ∣ n ↔ P.parent ∣ n ∧ ∀ i ∈ I, P.modulus i ∣ n := by
  constructor
  · intro h
    refine ⟨dvd_trans ⟨I.lcm P.modulus, rfl⟩ h, fun i hi => ?_⟩
    have h1 : P.modulus i ∣ I.lcm P.modulus := Finset.dvd_lcm hi
    exact dvd_trans (dvd_trans h1 ⟨P.parent, mul_comm _ _⟩) h
  · rintro ⟨h1, h2⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (P.coprime_parent_lcm hI) h1
      (Finset.lcm_dvd h2)

/-- "Every tag prime occurs in just one labelled pair.  Its presence in the
least common multiple therefore recovers whether that pair was selected." -/
theorem tag_dvd_iff {I : Finset ℕ} (hI : I ⊆ P.idx) {i : ℕ} (hi : i ∈ P.idx) :
    P.tag i ∣ P.parent * I.lcm P.modulus ↔ i ∈ I := by
  constructor
  · intro h
    have hprime : Prime (P.tag i) := (P.tag_prime i hi).prime
    have hlcm : I.lcm P.modulus ∣ ∏ j ∈ I, P.modulus j :=
      Finset.lcm_dvd fun j hj => Finset.dvd_prod_of_mem _ hj
    have hall : P.tag i ∣ P.parent * ∏ j ∈ I, P.modulus j :=
      dvd_trans h (mul_dvd_mul_left P.parent hlcm)
    rcases (Nat.Prime.dvd_mul (P.tag_prime i hi)).mp hall with hpar | hprod
    · exact absurd hpar (P.tag_not_dvd_parent i hi)
    · obtain ⟨j, hj, hdvd⟩ := (Prime.dvd_finset_prod_iff hprime P.modulus).mp hprod
      by_cases hij : i = j
      · exact hij ▸ hj
      · exact absurd hdvd (P.tag_not_dvd_other i hi j (hI hj) hij)
  · intro h
    have h1 : P.tag i ∣ P.modulus i := P.tag_dvd_modulus i hi
    have h2 : P.modulus i ∣ I.lcm P.modulus := Finset.dvd_lcm h
    exact dvd_trans (dvd_trans h1 h2) ⟨P.parent, mul_comm _ _⟩

/-- "Hence different subsets give distinct exponents." -/
theorem frameMap_injOn :
    Set.InjOn (fun I : Finset ℕ => P.parent * I.lcm P.modulus)
      (P.idx.powerset : Set (Finset ℕ)) := by
  intro I1 h1 I2 h2 heq
  have hI1 : I1 ⊆ P.idx := Finset.mem_powerset.mp (Finset.mem_coe.mp h1)
  have hI2 : I2 ⊆ P.idx := Finset.mem_powerset.mp (Finset.mem_coe.mp h2)
  simp only at heq
  ext i
  constructor
  · intro hi
    have hidx : i ∈ P.idx := hI1 hi
    have h := (P.tag_dvd_iff hI1 hidx).mpr hi
    rw [heq] at h
    exact (P.tag_dvd_iff hI2 hidx).mp h
  · intro hi
    have hidx : i ∈ P.idx := hI2 hi
    have h := (P.tag_dvd_iff hI2 hidx).mpr hi
    rw [← heq] at h
    exact (P.tag_dvd_iff hI1 hidx).mp h

/-- The paper's exact identity `f_{F_q}(n) = 1_{q ∣ n} 2^{Z_q(n)}`. -/
theorem incidenceCount_frame (n : ℕ) :
    incidenceCount P.frame n = if P.parent ∣ n then 2 ^ P.tagCount n else 0 := by
  classical
  have hcard : incidenceCount P.frame n
      = (P.idx.powerset.filter
          (fun I => P.parent * I.lcm P.modulus ∣ n)).card := by
    unfold incidenceCount frame
    rw [Finset.filter_image]
    refine Finset.card_image_of_injOn ?_
    exact Set.InjOn.mono (by
      intro I hI
      exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hI)).1)
      P.frameMap_injOn
  rw [hcard]
  by_cases hpn : P.parent ∣ n
  · rw [if_pos hpn]
    have hset : P.idx.powerset.filter (fun I => P.parent * I.lcm P.modulus ∣ n)
        = (P.idx.filter (fun i => P.modulus i ∣ n)).powerset := by
      ext I
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨hIsub, hdvd⟩
        intro i hi
        exact Finset.mem_filter.mpr ⟨hIsub hi, ((P.mem_dvd_iff hIsub n).mp hdvd).2 i hi⟩
      · intro hI
        have hIsub : I ⊆ P.idx := fun i hi => (Finset.mem_filter.mp (hI hi)).1
        refine ⟨hIsub, (P.mem_dvd_iff hIsub n).mpr ⟨hpn, fun i hi => ?_⟩⟩
        exact (Finset.mem_filter.mp (hI hi)).2
    rw [hset, Finset.card_powerset]
    rfl
  · rw [if_neg hpn]
    refine Finset.card_eq_zero.mpr ?_
    refine Finset.filter_eq_empty_iff.mpr ?_
    intro I hI
    intro hdvd
    exact hpn ((P.mem_dvd_iff (Finset.mem_powerset.mp hI) n).mp hdvd).1

/-- `q` itself belongs to `F_q`: "later positive terms, for example those
supplied by the exponent `q ∈ F_q`". -/
theorem parent_mem_frame : P.parent ∈ P.frame := by
  refine Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩
  simp

theorem frame_nonempty : P.frame.Nonempty := ⟨P.parent, P.parent_mem_frame⟩

/-- Each `q d p` belongs to `F_q`, so every modulus of the logarithmic majorant
below divides `lcm(F_q)`. -/
theorem parent_mul_modulus_mem_frame {i : ℕ} (hi : i ∈ P.idx) :
    P.parent * P.modulus i ∈ P.frame := by
  classical
  refine Finset.mem_image.mpr ⟨{i}, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_singleton] at hj
    exact hj ▸ hi
  · rw [Finset.lcm_singleton]
    simp [normalize_eq]

/-- Every exponent of `F_q` is a multiple of `q`; in particular all of them
exceed `max {L, A₀}` once `q` does. -/
theorem parent_dvd_of_mem_frame {a : ℕ} (ha : a ∈ P.frame) : P.parent ∣ a := by
  obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨I.lcm P.modulus, rfl⟩

theorem pos_of_mem_frame {a : ℕ} (ha : a ∈ P.frame) : 0 < a := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ha
  have hIsub : I ⊆ P.idx := Finset.mem_powerset.mp hI
  have hprodpos : 0 < ∏ i ∈ I, P.modulus i :=
    Finset.prod_pos fun i hi => P.modulus_pos i (hIsub hi)
  have hdvdprod : I.lcm P.modulus ∣ ∏ i ∈ I, P.modulus i :=
    Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi
  have hlcm : 0 < I.lcm P.modulus := Nat.pos_of_dvd_of_pos hdvdprod hprodpos
  exact Nat.mul_pos P.parent_prime.pos hlcm

/-- Every exponent divides `q ∏_{(d,p) ∈ 𝓘_q} d p`, so "all exponents are
squarefree" whenever that single product is. -/
theorem dvd_parent_mul_prod {a : ℕ} (ha : a ∈ P.frame) :
    a ∣ P.parent * ∏ i ∈ P.idx, P.modulus i := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ha
  have hIsub : I ⊆ P.idx := Finset.mem_powerset.mp hI
  have h1 : I.lcm P.modulus ∣ ∏ i ∈ I, P.modulus i :=
    Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi
  have h2 : (∏ i ∈ I, P.modulus i) ∣ ∏ i ∈ P.idx, P.modulus i :=
    Finset.prod_dvd_prod_of_subset I P.idx P.modulus hIsub
  exact mul_dvd_mul_left P.parent (dvd_trans h1 h2)

theorem squarefree_of_mem_frame
    (hsq : Squarefree (P.parent * ∏ i ∈ P.idx, P.modulus i))
    {a : ℕ} (ha : a ∈ P.frame) : Squarefree a :=
  hsq.squarefree_of_dvd (P.dvd_parent_mul_prod ha)

/-! ### The logarithmic majorant of one parent group -/

/-- The paper's majorant
`log(1 + f_{F_q}(n)) ≤ (log 2)(1_{q ∣ n} + ∑_{(d,p) ∈ 𝓘_q} 1_{q d p ∣ n})`. -/
theorem log_one_add_incidenceCount_le (n : ℕ) :
    Real.log (1 + (incidenceCount P.frame n : ℝ))
      ≤ Real.log 2 * ((if P.parent ∣ n then (1 : ℝ) else 0)
          + ∑ i ∈ P.idx, (if P.parent * P.modulus i ∣ n then (1 : ℝ) else 0)) := by
  classical
  by_cases hpn : P.parent ∣ n
  · have hcount : incidenceCount P.frame n = 2 ^ P.tagCount n := by
      rw [P.incidenceCount_frame n, if_pos hpn]
    have hterms : ∀ i ∈ P.idx,
        (if P.parent * P.modulus i ∣ n then (1 : ℝ) else 0)
          = (if P.modulus i ∣ n then (1 : ℝ) else 0) := by
      intro i hi
      have hiff : P.parent * P.modulus i ∣ n ↔ P.modulus i ∣ n := by
        constructor
        · intro h
          exact dvd_trans ⟨P.parent, mul_comm _ _⟩ h
        · intro h
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (P.parent_coprime_modulus i hi) hpn h
      by_cases h : P.modulus i ∣ n
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]
    have hsum : (∑ i ∈ P.idx, (if P.parent * P.modulus i ∣ n then (1 : ℝ) else 0))
        = (P.tagCount n : ℝ) := by
      rw [Finset.sum_congr rfl hterms, Finset.sum_boole]
      rfl
    rw [hcount, if_pos hpn, hsum]
    have hZ : (1 : ℝ) + (2 : ℝ) ^ P.tagCount n ≤ (2 : ℝ) ^ (P.tagCount n + 1) := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ P.tagCount n := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      linarith
    have hcast : ((2 ^ P.tagCount n : ℕ) : ℝ) = (2 : ℝ) ^ P.tagCount n := by
      push_cast; ring
    rw [hcast]
    have hpos : (0 : ℝ) < 1 + (2 : ℝ) ^ P.tagCount n := by positivity
    have hlog := Real.log_le_log hpos hZ
    rw [Real.log_pow] at hlog
    have hfin : ((P.tagCount n + 1 : ℕ) : ℝ) * Real.log 2
        = Real.log 2 * (1 + (P.tagCount n : ℝ)) := by
      push_cast; ring
    rw [hfin] at hlog
    exact hlog
  · have hcount : incidenceCount P.frame n = 0 := by
      rw [P.incidenceCount_frame n, if_neg hpn]
    have hterms : ∀ i ∈ P.idx,
        (if P.parent * P.modulus i ∣ n then (1 : ℝ) else 0) = 0 := by
      intro i hi
      refine if_neg (fun h => hpn ?_)
      exact dvd_trans ⟨P.modulus i, rfl⟩ h
    rw [hcount, if_neg hpn, Finset.sum_congr rfl hterms]
    simp

/-! ### The cost of that majorant -/

/-- The paper's cost `(log 2 / q)(1 + ∑_{(d,p) ∈ 𝓘_q} 1/(d p))` of the majorant
of `log(1 + f_{F_q})`, which for the constructed tag sets is
`(log 2 / q)(1 + ∑_{d ∣ L} S_{q,d}/d)`. -/
def majorantCost : ℝ :=
  Real.log 2 / P.parent * (1 + ∑ i ∈ P.idx, 1 / (P.modulus i : ℝ))

/-- The moduli of the majorant are pairwise distinct: the parent `q` is not one
of the `q d p`, and distinct labelled pairs have distinct moduli because a tag
prime divides its own modulus and no other. -/
theorem modulus_injOn : Set.InjOn P.modulus (P.idx : Set ℕ) := by
  intro i hi j hj heq
  by_contra hij
  have h1 : P.tag i ∣ P.modulus i := P.tag_dvd_modulus i (Finset.mem_coe.mp hi)
  rw [heq] at h1
  exact P.tag_not_dvd_other i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij h1

theorem parent_ne_parent_mul_modulus {i : ℕ} (hi : i ∈ P.idx) :
    P.parent ≠ P.parent * P.modulus i := by
  intro h
  have hpos := P.modulus_pos i hi
  have hcop := P.parent_coprime_modulus i hi
  have hone : P.modulus i = 1 := by
    have hq := P.parent_prime.pos
    nlinarith [h, hq, hpos]
  have hdvd : P.tag i ∣ 1 := hone ▸ P.tag_dvd_modulus i hi
  have := (P.tag_prime i hi).one_lt
  have := Nat.le_of_dvd Nat.one_pos hdvd
  omega

/-- The paper's cost bound `(log 2 / q)(1 + ∑_{d ∣ L} S_{q,d}/d) ≤ (log 2/q)(1 + 5D/H)`
in the form used: any uniform bound on the modulus reciprocal sum transfers. -/
theorem majorantCost_le {c : ℝ} (hc : (∑ i ∈ P.idx, 1 / (P.modulus i : ℝ)) ≤ c) :
    P.majorantCost ≤ Real.log 2 / P.parent * (1 + c) := by
  unfold majorantCost
  have hq : (0 : ℝ) < P.parent := by exact_mod_cast P.parent_prime.pos
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcoef : (0 : ℝ) ≤ Real.log 2 / P.parent := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hcoef

end ParentTagData

/-! ### The logarithmic cost of the whole support `F = ⋃_{q ∈ 𝓑} F_q`

"Since `f_F = ∑_q f_{F_q}` and `log(1 + ∑_q x_q) ≤ ∑_q log(1 + x_q)` for
`x_q ≥ 0`, we may sum the positive majorants", which gives

  `κ₁(F;1) ≤ ∑_{q ∈ 𝓑} (log 2 / q)(1 + ∑_{(d,p) ∈ 𝓘_q} 1/(d p))`. -/

/-- The moduli of the paper's majorant of `log(1 + f_{F_q})`: the parent `q`
itself and the `q d p`. -/
def majorantSupport (Q : ParentTagData) : Finset ℕ :=
  insert Q.parent (Q.idx.image (fun i => Q.parent * Q.modulus i))

theorem mul_modulus_injOn (Q : ParentTagData) :
    Set.InjOn (fun i => Q.parent * Q.modulus i) (Q.idx : Set ℕ) := by
  intro i hi j hj heq
  have hq : 0 < Q.parent := Q.parent_prime.pos
  simp only at heq
  exact Q.modulus_injOn hi hj (Nat.eq_of_mul_eq_mul_left hq heq)

theorem parent_notMem_image (Q : ParentTagData) :
    Q.parent ∉ Q.idx.image (fun i => Q.parent * Q.modulus i) := by
  intro h
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
  exact Q.parent_ne_parent_mul_modulus hi heq.symm

theorem sum_majorantSupport (Q : ParentTagData) (g : ℕ → ℝ) :
    ∑ d ∈ majorantSupport Q, g d
      = g Q.parent + ∑ i ∈ Q.idx, g (Q.parent * Q.modulus i) := by
  classical
  unfold majorantSupport
  rw [Finset.sum_insert (parent_notMem_image Q),
    Finset.sum_image (fun i hi j hj h =>
      mul_modulus_injOn Q (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) h)]

theorem majorantSupport_subset_frame (Q : ParentTagData) :
    majorantSupport Q ⊆ Q.frame := by
  intro d hd
  simp only [majorantSupport, Finset.mem_insert] at hd
  rcases hd with rfl | hd'
  · exact Q.parent_mem_frame
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd'
    exact Q.parent_mul_modulus_mem_frame hi

/-- The cost of the paper's majorant for one parent is
`(log 2 / q)(1 + ∑_{(d,p) ∈ 𝓘_q} 1/(d p))`. -/
theorem cost_majorantSupport (Q : ParentTagData) :
    ∑ d ∈ majorantSupport Q, Real.log 2 / (d : ℝ) = Q.majorantCost := by
  rw [sum_majorantSupport]
  unfold ParentTagData.majorantCost
  have hq : (0 : ℝ) < (Q.parent : ℝ) := by exact_mod_cast Q.parent_prime.pos
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hw : (0 : ℝ) < (Q.modulus i : ℝ) := by exact_mod_cast Q.modulus_pos i hi
  push_cast
  field_simp

theorem sum_majorantSupport_dvd (Q : ParentTagData) (s : ℕ) :
    ∑ d ∈ majorantSupport Q, (if d ∣ s then Real.log 2 else 0)
      = Real.log 2 * ((if Q.parent ∣ s then (1 : ℝ) else 0)
          + ∑ i ∈ Q.idx, (if Q.parent * Q.modulus i ∣ s then (1 : ℝ) else 0)) := by
  rw [sum_majorantSupport, mul_add, Finset.mul_sum]
  congr 1
  · split_ifs <;> ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring

/-- The summed majorant coefficients of the whole support. -/
def totalCoefficient (B : Finset ℕ) (P : ℕ → ParentTagData) (d : ℕ) : ℝ :=
  ∑ q ∈ B, (if d ∈ majorantSupport (P q) then Real.log 2 else 0)

theorem totalCoefficient_nonneg (B : Finset ℕ) (P : ℕ → ParentTagData) (d : ℕ) :
    0 ≤ totalCoefficient B P d := by
  unfold totalCoefficient
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · exact (Real.log_pos (by norm_num)).le
  · exact le_rfl

theorem sum_divisors_totalCoefficient (B : Finset ℕ) (P : ℕ → ParentTagData)
    {s : ℕ} (hs : 0 < s) :
    ∑ d ∈ s.divisors, totalCoefficient B P d
      = ∑ q ∈ B, ∑ d ∈ majorantSupport (P q), (if d ∣ s then Real.log 2 else 0) := by
  classical
  have hconv : ∀ d : ℕ, (if d ∣ s then Real.log 2 else 0)
      = (if d ∈ s.divisors then Real.log 2 else 0) := by
    intro d
    by_cases h : d ∣ s
    · rw [if_pos h, if_pos (Nat.mem_divisors.mpr ⟨h, hs.ne'⟩)]
    · rw [if_neg h, if_neg (fun hc => h (Nat.mem_divisors.mp hc).1)]
  simp only [hconv, totalCoefficient]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_comm]

theorem divisorMajorantCost_totalCoefficient (B : Finset ℕ) (P : ℕ → ParentTagData)
    (D : Finset ℕ) (hsub : ∀ q ∈ B, majorantSupport (P q) ⊆ D) :
    divisorMajorantCost D (totalCoefficient B P) = ∑ q ∈ B, (P q).majorantCost := by
  classical
  unfold divisorMajorantCost totalCoefficient
  have hstep : ∀ d ∈ D,
      (∑ q ∈ B, (if d ∈ majorantSupport (P q) then Real.log 2 else 0)) / (d : ℝ)
        = ∑ q ∈ B, (if d ∈ majorantSupport (P q) then Real.log 2 else 0) / (d : ℝ) := by
    intro d _
    rw [Finset.sum_div]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hzero : ∀ d ∈ D, d ∉ majorantSupport (P q) →
      (if d ∈ majorantSupport (P q) then Real.log 2 else 0) / (d : ℝ) = 0 := by
    intro d _ hnot
    rw [if_neg hnot, zero_div]
  rw [← Finset.sum_subset (hsub q hq) hzero, ← cost_majorantSupport (P q)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [if_pos hd]

/-- The paper's `log(1 + ∑_q x_q) ≤ ∑_q log(1 + x_q)` for `x_q ≥ 0`. -/
theorem log_one_add_sum_le (B : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ q ∈ B, 0 ≤ x q) :
    Real.log (1 + ∑ q ∈ B, x q) ≤ ∑ q ∈ B, Real.log (1 + x q) := by
  classical
  revert hx
  induction B using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro hx
      have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
      have hxs : ∀ q ∈ s, 0 ≤ x q := fun q hq => hx q (Finset.mem_insert_of_mem hq)
      have hsum0 : 0 ≤ ∑ q ∈ s, x q := Finset.sum_nonneg hxs
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hkey : (1 : ℝ) + (x a + ∑ q ∈ s, x q) ≤ (1 + x a) * (1 + ∑ q ∈ s, x q) := by
        nlinarith
      have hposl : (0 : ℝ) < 1 + (x a + ∑ q ∈ s, x q) := by linarith
      have h1 := Real.log_le_log hposl hkey
      rw [Real.log_mul (by linarith) (by linarith)] at h1
      have h2 := ih hxs
      linarith

/-- "Different parent primes give disjoint sets", so `f_F = ∑_q f_{F_q}`. -/
theorem incidenceCount_biUnion (B : Finset ℕ) (G : ℕ → Finset ℕ)
    (hdisj : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (G i) (G j)) (n : ℕ) :
    incidenceCount (B.biUnion G) n = ∑ q ∈ B, incidenceCount (G q) n := by
  classical
  unfold incidenceCount
  rw [Finset.filter_biUnion]
  refine Finset.card_biUnion ?_
  intro i hi j hj hij
  exact Finset.disjoint_filter_filter
    (hdisj i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij)

theorem logMajorantCosts_bddBelow (F : Finset ℕ) (t : ℝ) :
    BddBelow (logMajorantCosts F t) := by
  refine ⟨0, ?_⟩
  rintro K ⟨c, hc0, -, rfl⟩
  exact divisorMajorantCost_nonneg hc0

/-- The paper's cost estimate for the whole support:

  `κ₁(F;1) ≤ ∑_{q ∈ 𝓑} (log 2 / q)(1 + ∑_{(d,p) ∈ 𝓘_q} 1/(d p))`,

which for the constructed tag sets is `≤ (5 log 2 / D)(1 + 5D/H) ≤ 30 log 2/H`.
The hypothesis is the paper's "different parent primes give disjoint sets". -/
theorem kappaOne_biUnion_frame_le (B : Finset ℕ) (P : ℕ → ParentTagData)
    (hdisj : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (P i).frame (P j).frame) :
    kappaOne (B.biUnion fun q => (P q).frame) 1 ≤ ∑ q ∈ B, (P q).majorantCost := by
  classical
  set F : Finset ℕ := B.biUnion (fun q => (P q).frame) with hFdef
  have hF0 : (0 : ℕ) ∉ F := by
    intro h
    obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.mp h
    exact absurd ((P q).pos_of_mem_frame hq) (lt_irrefl 0)
  have hQ0 : frameLcm F ≠ 0 := frameLcm_ne_zero hF0
  have hsub : ∀ q ∈ B, majorantSupport (P q) ⊆ (frameLcm F).divisors := by
    intro q hq d hd
    have hdF : d ∈ F := by
      refine Finset.mem_biUnion.mpr ⟨q, hq, ?_⟩
      exact majorantSupport_subset_frame (P q) hd
    exact Nat.mem_divisors.mpr ⟨dvd_frameLcm hdF, hQ0⟩
  have hcon : ∀ s ∈ (frameLcm F).divisors,
      Real.log (1 + (incidenceCount F s : ℝ) / 1)
        ≤ ∑ d ∈ s.divisors, totalCoefficient B P d := by
    intro s hs
    have hspos : 0 < s := Nat.pos_of_mem_divisors hs
    have hsplit : incidenceCount F s = ∑ q ∈ B, incidenceCount ((P q).frame) s :=
      incidenceCount_biUnion B (fun q => (P q).frame) hdisj s
    have hcast : ((incidenceCount F s : ℕ) : ℝ)
        = ∑ q ∈ B, ((incidenceCount ((P q).frame) s : ℕ) : ℝ) := by
      rw [hsplit]
      push_cast
      ring
    rw [div_one, hcast]
    have hstep1 : Real.log (1 + ∑ q ∈ B, ((incidenceCount ((P q).frame) s : ℕ) : ℝ))
        ≤ ∑ q ∈ B, Real.log (1 + ((incidenceCount ((P q).frame) s : ℕ) : ℝ)) :=
      log_one_add_sum_le B (fun q => ((incidenceCount ((P q).frame) s : ℕ) : ℝ))
        (fun q _ => Nat.cast_nonneg _)
    have hstep2 : ∀ q ∈ B,
        Real.log (1 + ((incidenceCount ((P q).frame) s : ℕ) : ℝ))
          ≤ ∑ d ∈ majorantSupport (P q), (if d ∣ s then Real.log 2 else 0) := by
      intro q _
      rw [sum_majorantSupport_dvd]
      exact (P q).log_one_add_incidenceCount_le s
    have hstep3 : (∑ q ∈ B, Real.log (1 + ((incidenceCount ((P q).frame) s : ℕ) : ℝ)))
        ≤ ∑ q ∈ B, ∑ d ∈ majorantSupport (P q), (if d ∣ s then Real.log 2 else 0) :=
      Finset.sum_le_sum hstep2
    rw [sum_divisors_totalCoefficient B P hspos]
    linarith
  have hmem : divisorMajorantCost (frameLcm F).divisors (totalCoefficient B P)
      ∈ logMajorantCosts F 1 :=
    ⟨totalCoefficient B P, totalCoefficient_nonneg B P, hcon, rfl⟩
  have hle : kappaOne F 1
      ≤ divisorMajorantCost (frameLcm F).divisors (totalCoefficient B P) :=
    csInf_le (logMajorantCosts_bddBelow F 1) hmem
  rw [divisorMajorantCost_totalCoefficient B P _ hsub] at hle
  exact hle

#print axioms ParentTagData.incidenceCount_frame
#print axioms ParentTagData.frameMap_injOn
#print axioms ParentTagData.log_one_add_incidenceCount_le
#print axioms ParentTagData.parent_mul_modulus_mem_frame
#print axioms ParentTagData.squarefree_of_mem_frame
#print axioms ParentTagData.modulus_injOn
#print axioms ParentTagData.majorantCost_le
#print axioms cost_majorantSupport
#print axioms log_one_add_sum_le
#print axioms incidenceCount_biUnion
#print axioms divisorMajorantCost_totalCoefficient
#print axioms kappaOne_biUnion_frame_le

end ErdosProblems.Erdos257.PaperCompleteR21

end
