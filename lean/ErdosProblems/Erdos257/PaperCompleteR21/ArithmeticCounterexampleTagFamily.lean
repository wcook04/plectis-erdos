import ErdosProblems.Erdos257.PaperCompleteR21.ArithmeticCounterexampleEncoding

/-!
# Building one parent group from the selected tag sets (long #257, line 9212)

The step of the long Erdős #257 `thm` "arithmetic logarithmic counterexample"
(`paper/reasoning-parts/erdos257/a257_front.tex:9212`) that turns the chosen tag
sets into the labelled-pair data of one parent prime.  The paper writes

  `𝓘_q = {(d, p) : d ∣ L, p ∈ T_{q,d}}`

and relies on "every tag prime occurs in just one labelled pair".  That is
exactly the statement that the tag sets `T_{q,d}` are pairwise disjoint as `d`
runs over the divisors of `L`, so the tag prime `p` already determines its
partner `d`.  `TagFamily` below records the selected data with the separation
properties the construction arranges, `tagIndex` is `𝓘_q` indexed by the tag
prime itself, `tagModulus p` recovers `d p`, and `TagFamily.toParentTagData`
produces the `ParentTagData` of
`ArithmeticCounterexampleEncoding.lean`, whose `incidenceCount_frame` is then
the paper's `f_{F_q}(n) = 1_{q ∣ n} 2^{Z_q(n)}` for this group.

`sum_inv_tagModulus` is the cost input: the reciprocal sum over `𝓘_q` is
`∑_{d ∣ L} S_{q,d}/d`, which is what `ParentTagData.majorantCost` needs in order
to become the paper's `(log 2 / q)(1 + ∑_{d ∣ L} S_{q,d}/d)`.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset

/-- The tag data selected for one parent prime `q`: for each divisor `d` of `L`
a finite set `T_{q,d}` of tag primes, pairwise disjoint as `d` varies, none
dividing `L` and none equal to the parent, with the parent above `L`. -/
structure TagFamily where
  /-- The modulus `L = ∏_{p ∈ P} p`. -/
  L : ℕ
  /-- The parent prime `q`. -/
  parent : ℕ
  /-- The tag sets `T_{q,d}`. -/
  tags : ℕ → Finset ℕ
  L_pos : 0 < L
  parent_prime : parent.Prime
  L_lt_parent : L < parent
  tag_prime : ∀ d ∈ L.divisors, ∀ p ∈ tags d, p.Prime
  tag_ne_parent : ∀ d ∈ L.divisors, ∀ p ∈ tags d, p ≠ parent
  tag_not_dvd_L : ∀ d ∈ L.divisors, ∀ p ∈ tags d, ¬ p ∣ L
  tag_disjoint : ∀ d ∈ L.divisors, ∀ d' ∈ L.divisors, d ≠ d' →
    Disjoint (tags d) (tags d')

namespace TagFamily

variable (T : TagFamily)

/-- The paper's `𝓘_q`, indexed by the tag prime itself. -/
def tagIndex : Finset ℕ := T.L.divisors.biUnion T.tags

/-- The modulus `d p` of the labelled pair carrying the tag prime `p`. -/
def tagModulus (p : ℕ) : ℕ := ∑ d ∈ T.L.divisors, (if p ∈ T.tags d then d * p else 0)

theorem mem_tagIndex_iff {p : ℕ} :
    p ∈ T.tagIndex ↔ ∃ d ∈ T.L.divisors, p ∈ T.tags d := by
  unfold tagIndex
  exact Finset.mem_biUnion

/-- "Every tag prime occurs in just one labelled pair": the disjointness of the
tag sets makes `p` determine `d`. -/
theorem tagModulus_eq {d p : ℕ} (hd : d ∈ T.L.divisors) (hp : p ∈ T.tags d) :
    T.tagModulus p = d * p := by
  classical
  have h0 : ∀ b ∈ T.L.divisors, b ≠ d → (if p ∈ T.tags b then b * p else 0) = 0 := by
    intro b hb hbd
    refine if_neg ?_
    intro hpb
    exact (Finset.disjoint_left.mp (T.tag_disjoint b hb d hd hbd) hpb) hp
  unfold tagModulus
  rw [Finset.sum_eq_single_of_mem d hd h0, if_pos hp]

theorem tagIndex_prime {p : ℕ} (hp : p ∈ T.tagIndex) : p.Prime := by
  obtain ⟨d, hd, hpd⟩ := T.mem_tagIndex_iff.mp hp
  exact T.tag_prime d hd p hpd

theorem tagModulus_pos {p : ℕ} (hp : p ∈ T.tagIndex) : 0 < T.tagModulus p := by
  obtain ⟨d, hd, hpd⟩ := T.mem_tagIndex_iff.mp hp
  rw [T.tagModulus_eq hd hpd]
  exact Nat.mul_pos (Nat.pos_of_mem_divisors hd) (T.tag_prime d hd p hpd).pos

/-- The `ParentTagData` of one parent group, with the tag prime as the index of
its labelled pair. -/
def toParentTagData : ParentTagData where
  parent := T.parent
  idx := T.tagIndex
  modulus := T.tagModulus
  tag := fun p => p
  parent_prime := T.parent_prime
  tag_prime := fun i hi => T.tagIndex_prime hi
  tag_dvd_modulus := by
    intro i hi
    obtain ⟨d, hd, hid⟩ := T.mem_tagIndex_iff.mp hi
    rw [T.tagModulus_eq hd hid]
    exact dvd_mul_left i d
  modulus_pos := fun i hi => T.tagModulus_pos hi
  tag_not_dvd_parent := by
    intro i hi hdvd
    have hip : i.Prime := T.tagIndex_prime hi
    obtain ⟨d, hd, hid⟩ := T.mem_tagIndex_iff.mp hi
    have heq : i = T.parent :=
      (Nat.prime_dvd_prime_iff_eq hip T.parent_prime).mp hdvd
    exact T.tag_ne_parent d hd i hid heq
  tag_not_dvd_other := by
    intro i hi j hj hij hdvd
    obtain ⟨di, hdi, hidi⟩ := T.mem_tagIndex_iff.mp hi
    obtain ⟨dj, hdj, hjdj⟩ := T.mem_tagIndex_iff.mp hj
    have hip : i.Prime := T.tag_prime di hdi i hidi
    have hjp : j.Prime := T.tag_prime dj hdj j hjdj
    rw [T.tagModulus_eq hdj hjdj] at hdvd
    rcases (Nat.Prime.dvd_mul hip).mp hdvd with h | h
    · exact T.tag_not_dvd_L di hdi i hidi (h.trans (Nat.mem_divisors.mp hdj).1)
    · exact hij ((Nat.prime_dvd_prime_iff_eq hip hjp).mp h)
  parent_coprime_modulus := by
    intro i hi
    obtain ⟨d, hd, hid⟩ := T.mem_tagIndex_iff.mp hi
    rw [T.tagModulus_eq hd hid]
    refine (Nat.Prime.coprime_iff_not_dvd T.parent_prime).mpr ?_
    intro hdvd
    rcases (Nat.Prime.dvd_mul T.parent_prime).mp hdvd with h | h
    · have hdL : d ∣ T.L := (Nat.mem_divisors.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have h1 : T.parent ≤ d := Nat.le_of_dvd hdpos h
      have h2 : d ≤ T.L := Nat.le_of_dvd T.L_pos hdL
      have h3 := T.L_lt_parent
      omega
    · have hip : i.Prime := T.tag_prime d hd i hid
      have heq : T.parent = i := (Nat.prime_dvd_prime_iff_eq T.parent_prime hip).mp h
      exact T.tag_ne_parent d hd i hid heq.symm

theorem toParentTagData_parent : T.toParentTagData.parent = T.parent := rfl

theorem toParentTagData_idx : T.toParentTagData.idx = T.tagIndex := rfl

theorem toParentTagData_modulus : T.toParentTagData.modulus = T.tagModulus := rfl

/-- The cost input: `∑_{(d,p) ∈ 𝓘_q} 1/(d p) = ∑_{d ∣ L} S_{q,d}/d`. -/
theorem sum_inv_tagModulus :
    (∑ p ∈ T.tagIndex, 1 / (T.tagModulus p : ℝ))
      = ∑ d ∈ T.L.divisors, (1 / (d : ℝ)) * ∑ p ∈ T.tags d, 1 / (p : ℝ) := by
  classical
  have hdisj : (↑T.L.divisors : Set ℕ).PairwiseDisjoint T.tags := by
    intro d hd d' hd' hne
    exact T.tag_disjoint d (Finset.mem_coe.mp hd) d' (Finset.mem_coe.mp hd') hne
  unfold tagIndex
  rw [Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [T.tagModulus_eq hd hp]
  push_cast
  rw [one_div_mul_one_div]

/-- "Their minimum is greater than `max{L, A₀}`": every exponent of `F_q` is a
positive multiple of the parent prime. -/
theorem parent_le_of_mem_frame {a : ℕ} (ha : a ∈ T.toParentTagData.frame) :
    T.parent ≤ a :=
  Nat.le_of_dvd (T.toParentTagData.pos_of_mem_frame ha)
    (T.toParentTagData.parent_dvd_of_mem_frame ha)

#print axioms tagModulus_eq
#print axioms toParentTagData
#print axioms sum_inv_tagModulus
#print axioms parent_le_of_mem_frame

end TagFamily

end ErdosProblems.Erdos257.PaperCompleteR21

end
