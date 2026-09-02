import Erdos249257.TotientMahlerDefect

/-!
# Linear independence of totients along odd-slope affine forms

Let `L_i(n) = a_i n + b_i` be a finite family of affine forms with

* `a_i` **odd** and positive,
* `b_i < a_i` and `gcd (a_i, b_i) = 1`,
* `a_j b_i ≠ a_i b_j` for `i ≠ j` (pairwise non-proportional).

This file proves that the sequences `n ↦ φ (L_i n)` are linearly independent
over `ℚ`.

## Provenance: this is a formalisation of known mathematics

This statement is **subsumed by Greg Martin, "Simultaneous inequalities among
values of the Euler phi-function", arXiv:math/0603053 (2006), Theorem 1**, which
assumes only that the `a_i` are positive integers and that `a_i b_j ≠ a_j b_i`,
and concludes that for *every* constant `C > 0` the simultaneous ratio gaps
`φ(a_1 n + b_1)/φ(a_2 n + b_2) > C, …` hold on a set of positive lower density.
Linear independence over `ℝ` follows immediately by taking `C` larger than
`(Σ_{i≠t}|c_i|)/|c_t|` and using Martin's symmetry remark to put the chosen
channel first. Martin's Corollary 4 gives the same for `σ`.

Martin therefore needs neither the oddness of the slopes, nor primitivity, nor
`b_i < a_i`, and proves strictly more. The contribution here is a **Lean
formalisation, by an independent finite-determinant proof, of a corollary of
Martin's theorem** — proof engineering, not new mathematics. Do not describe it
as an original result.

What remains unlocated in the literature is the *exact finite-level rank* of the
`k`-kernel of `φ`; see `docs/formal_math/odd_slope_affine_totient_independence.md`.

The proof reuses, verbatim, the CRT--Dirichlet separation architecture already
built for the dyadic totient kernel in `Erdos249257.TotientMahlerDefect`:
`exists_large_distinct_primes_modEq_one`, `exists_affine_root_mod_prime`,
`affine_target_coprime_of_cross`, `paritySeparatedMatrix_det_ne_zero` and
`linearIndependent_of_separatedMinorCertificate` are all already generic.

The one place where odd slopes are *easier* than the dyadic case is the
two-adic depth.  In the dyadic family the slopes are powers of two, so a
channel's value cannot be steered into a prescribed odd class modulo `2^K`;
the dyadic proof therefore carries a column-dependent depth
(`totientAffineCore`, `exists_totientAffineCore_depth`) and must bound it.
Here every slope is invertible modulo `2^K`, so *every* channel can be driven
to `3 mod 8` simultaneously and the depth is the constant `1`.  That collapses
the depth bookkeeping entirely.

Nothing here concerns irrationality; these are structural independence
statements about Euler's totient along affine progressions.
-/

namespace Erdos249257

open Module Matrix

/-- A finite family of primitive, pairwise non-proportional affine forms with
odd slopes. -/
structure OddSlopeAffineFamily (ι : Type*) [Fintype ι] [DecidableEq ι] where
  slope : ι → ℕ
  residue : ι → ℕ
  slope_odd : ∀ i, Odd (slope i)
  residue_lt : ∀ i, residue i < slope i
  coprime : ∀ i, (slope i).Coprime (residue i)
  cross_ne : ∀ ⦃i j⦄, i ≠ j → slope j * residue i ≠ slope i * residue j

namespace OddSlopeAffineFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : OddSlopeAffineFamily ι)

/-- The natural value of channel `i` at input `n`. -/
def value (i : ι) (n : ℕ) : ℕ := F.slope i * n + F.residue i

/-- The rational-valued totient sequence of channel `i`. -/
def family : ι → ℕ → ℚ := fun i n => Nat.totient (F.value i n)

theorem slope_pos (i : ι) : 0 < F.slope i := by
  obtain ⟨k, hk⟩ := F.slope_odd i
  omega

theorem slope_coprime_two_pow (i : ι) (k : ℕ) : (F.slope i).Coprime (2 ^ k) :=
  (F.slope_odd i).coprime_two_right.pow_right k

/-- Every odd-slope channel can be steered into the class `3 mod 8`: there is
an input residue `c < 8` with `L_i c ≡ 3 [MOD 8]`. -/
theorem exists_base_residue (i : ι) :
    ∃ c < 8, F.value i c ≡ 3 [MOD 8] := by
  have hcop : (F.slope i).Coprime 8 := by
    simpa using F.slope_coprime_two_pow i 3
  obtain ⟨x, hxlt, hx⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (3 + (8 - F.residue i % 8)) hcop
      (by norm_num)
  refine ⟨x, hxlt, ?_⟩
  show (F.slope i * x + F.residue i) % 8 = 3 % 8
  rw [Nat.add_mod, hx]
  omega

/-- A CRT--Dirichlet row for target channel `i`: the target value is prime and
lies in `3 mod 8`, while every other channel picks up a fresh prime divisor
congruent to `1` modulo `8`. -/
structure PrimeRow (i : ι) where
  n : ℕ
  targetPrime : (F.value i n).Prime
  targetMod : F.value i n ≡ 3 [MOD 8]
  offPrime : ∀ j : ι, j ≠ i → ℕ
  offPrime_prime : ∀ (j : ι) (hji : j ≠ i), (offPrime j hji).Prime
  offPrime_modEq : ∀ (j : ι) (hji : j ≠ i), offPrime j hji ≡ 1 [MOD 8]
  offPrime_dvd : ∀ (j : ι) (hji : j ≠ i), offPrime j hji ∣ F.value j n

set_option maxHeartbeats 1000000 in
/-- Because every slope is odd, *every* channel can simultaneously be driven
into `3 mod 8`; this is the step the dyadic family cannot perform. -/
theorem exists_primeRow (i : ι) : Nonempty (F.PrimeRow i) := by
  classical
  let κ := {j : ι // j ≠ i}
  let T := 8
  let A := Finset.univ.sup fun j : ι => F.slope j
  let R := Finset.univ.sup fun j : ι => F.residue j
  let B := T + (A + 1) * (R + 1)
  have hT_pos : 0 < T := by norm_num [T]
  have hA (j : ι) : F.slope j ≤ A := Finset.le_sup (Finset.mem_univ j)
  have hR (j : ι) : F.residue j ≤ R := Finset.le_sup (Finset.mem_univ j)
  have hA_lt_B (j : ι) : F.slope j < B := by
    have hprod : A < (A + 1) * (R + 1) :=
      (Nat.lt_succ_self A).trans_le (Nat.le_mul_of_pos_right (A + 1) (Nat.succ_pos R))
    exact (hA j).trans_lt (hprod.trans_le (Nat.le_add_left _ _))
  have hT_lt_B : T < B := by
    have : 0 < (A + 1) * (R + 1) := by positivity
    omega
  have hcross_lt_B (j k : ι) : F.slope j * F.residue k < B := by
    have hmul : F.slope j * F.residue k ≤ A * R := Nat.mul_le_mul (hA j) (hR k)
    have hstrict : A * R < (A + 1) * (R + 1) := by nlinarith
    exact hmul.trans_lt (hstrict.trans_le (Nat.le_add_left _ _))
  obtain ⟨q, hq_inj, hq⟩ := exists_large_distinct_primes_modEq_one (ι := κ) 3 B
  have hroot_exists (j : κ) :
      ∃ x < q j, q j ∣ F.slope j.val * x + F.residue j.val :=
    exists_affine_root_mod_prime (F.slope_pos j.val)
      ((hA_lt_B j.val).trans (hq j).2.2) (hq j).1
  let root : κ → ℕ := fun j => Classical.choose (hroot_exists j)
  have hroot_dvd (j : κ) :
      q j ∣ F.slope j.val * root j + F.residue j.val :=
    (Classical.choose_spec (hroot_exists j)).2
  obtain ⟨c, _, hc⟩ := F.exists_base_residue i
  let modulus : Option κ → ℕ
    | none => T
    | some j => q j
  let residue : Option κ → ℕ
    | none => c
    | some j => root j
  have hmodulus_ne (x : Option κ) : modulus x ≠ 0 := by
    cases x with
    | none => exact hT_pos.ne'
    | some j => exact (hq j).1.ne_zero
  have hmodulus_pairwise :
      Set.Pairwise (↑(Finset.univ : Finset (Option κ)) : Set (Option κ))
        (Function.onFun Nat.Coprime modulus) := by
    intro x _ y _ hxy
    have hnotT (j : κ) : ¬q j ∣ T :=
      Nat.not_dvd_of_pos_of_lt hT_pos (hT_lt_B.trans (hq j).2.2)
    cases x with
    | none =>
        cases y with
        | none => exact (hxy rfl).elim
        | some j => exact ((hq j).1.coprime_iff_not_dvd.mpr (hnotT j)).symm
    | some j =>
        cases y with
        | none => exact (hq j).1.coprime_iff_not_dvd.mpr (hnotT j)
        | some k =>
            have hjk : j ≠ k := fun h => hxy (by simp [h])
            apply ((hq j).1.coprime_iff_not_dvd).2
            intro hdvd
            exact (fun h => hjk (hq_inj h))
              ((((hq k).1.dvd_iff_eq (hq j).1.ne_one).mp hdvd)).symm
  let crt := Nat.chineseRemainderOfFinset residue modulus Finset.univ
    (fun x _ => hmodulus_ne x) hmodulus_pairwise
  let Q := ∏ x : Option κ, modulus x
  have hcrt (x : Option κ) : crt.val ≡ residue x [MOD modulus x] :=
    crt.property x (Finset.mem_univ x)
  have hcrt_lt : crt.val < Q :=
    Nat.chineseRemainderOfFinset_lt_prod residue modulus
      (fun x _ => hmodulus_ne x) hmodulus_pairwise
  have hQ_ne : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => hmodulus_ne x
  have hmodulus_dvd_Q (x : Option κ) : modulus x ∣ Q :=
    Finset.dvd_prod_of_mem modulus (Finset.mem_univ x)
  let targetStep := F.slope i * Q
  let targetBase := F.value i crt.val
  have htargetBase_lt : targetBase < targetStep := by
    have hsucc : crt.val + 1 ≤ Q := Nat.succ_le_iff.mpr hcrt_lt
    have hr := F.residue_lt i
    dsimp only [targetBase, targetStep, value]
    calc F.slope i * crt.val + F.residue i
        < F.slope i * crt.val + F.slope i := Nat.add_lt_add_left hr _
      _ = F.slope i * (crt.val + 1) := by ring
      _ ≤ F.slope i * Q := Nat.mul_le_mul_left _ hsucc
  -- the base value already sits in `3 mod 8`
  have htargetBase_mod : targetBase ≡ 3 [MOD 8] := by
    have hbase := hcrt (none : Option κ)
    simp only [modulus, residue, T] at hbase
    have : F.value i crt.val ≡ F.value i c [MOD 8] :=
      (hbase.mul_left (F.slope i)).add_right (F.residue i)
    exact this.trans hc
  have htargetBase_odd : Odd targetBase := by
    have h := htargetBase_mod
    rw [Nat.ModEq] at h
    rw [Nat.odd_iff]
    omega
  have htarget_coprime_slope : targetBase.Coprime (F.slope i) := by
    dsimp only [targetBase, value]
    rw [add_comm, Nat.coprime_add_mul_left_left]
    exact (F.coprime i).symm
  have htarget_coprime_Q : targetBase.Coprime Q := by
    rw [Nat.coprime_prod_right_iff]
    intro x _
    cases x with
    | none =>
        dsimp only [modulus, T]
        simpa using htargetBase_odd.coprime_two_right.pow_right 3
    | some j =>
        have hoffDvd : q j ∣ F.value j.val crt.val := by
          have hm := hcrt (some j)
          simp only [modulus, residue] at hm
          exact Nat.modEq_zero_iff_dvd.mp
            (((hm.mul_left (F.slope j.val)).add_right (F.residue j.val)).trans
              (Nat.modEq_zero_iff_dvd.mpr (hroot_dvd j)))
        exact affine_target_coprime_of_cross (hq j).1
          (F.cross_ne (fun h => j.property h.symm))
          ((hcross_lt_B j.val i).trans (hq j).2.2)
          ((hcross_lt_B i j.val).trans (hq j).2.2) hoffDvd
  obtain ⟨p, hp_gt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq targetStep
      (mul_ne_zero (F.slope_pos i).ne' hQ_ne)
      (htarget_coprime_slope.mul_right htarget_coprime_Q)
  have hbase_le_p : targetBase ≤ p := htargetBase_lt.le.trans hp_gt.le
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hbase_le_p).mp hpmod.symm
  have hbridge : targetStep * t = F.slope i * Q * t := rfl
  have hp_eq : p = targetBase + targetStep * t := by omega
  refine ⟨⟨crt.val + Q * t, ?_, ?_, fun j hji => q ⟨j, hji⟩,
    fun j hji => (hq ⟨j, hji⟩).1, fun j hji => ?_, fun j hji => ?_⟩⟩
  · have hval : F.value i (crt.val + Q * t) = p := by
      dsimp only [value] at *
      dsimp only [targetBase, targetStep, value] at hp_eq
      rw [hp_eq]; ring
    exact hval ▸ hp
  · have hval : F.value i (crt.val + Q * t) = targetBase + targetStep * t := by
      dsimp only [targetBase, targetStep, value]; ring
    rw [hval]
    have hTQ : (8 : ℕ) ∣ Q := by
      simpa [modulus, T] using hmodulus_dvd_Q (none : Option κ)
    have hstep : targetStep * t ≡ 0 [MOD 8] :=
      Nat.modEq_zero_iff_dvd.mpr
        (Dvd.dvd.mul_right (Dvd.dvd.mul_left hTQ (F.slope i)) t)
    simpa using htargetBase_mod.add hstep
  · exact (hq ⟨j, hji⟩).2.1
  · have hbaseDvd : q ⟨j, hji⟩ ∣ F.value j crt.val := by
      have hm := hcrt (some ⟨j, hji⟩)
      simp only [modulus, residue] at hm
      exact Nat.modEq_zero_iff_dvd.mp
        (((hm.mul_left (F.slope j)).add_right (F.residue j)).trans
          (Nat.modEq_zero_iff_dvd.mpr (hroot_dvd ⟨j, hji⟩)))
    have hqdQ : q ⟨j, hji⟩ ∣ Q := hmodulus_dvd_Q (some ⟨j, hji⟩)
    rw [show F.value j (crt.val + Q * t)
        = F.value j crt.val + F.slope j * Q * t by dsimp only [value]; ring]
    exact dvd_add hbaseDvd
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqdQ (F.slope j)) t)

/-- Every entry of an odd-slope evaluation row is even, the diagonal has exact
two-adic depth one, and every off-diagonal entry has depth at least three. -/
noncomputable def separatedMinorCertificate : SeparatedMinorCertificate F.family := by
  classical
  have hrow : ∀ i : ι, F.PrimeRow i := fun i => Classical.choice (F.exists_primeRow i)
  let row : ι → ℕ := fun i => (hrow i).n
  let M : Matrix ι ι ℕ := fun i j => Nat.totient (F.value j (row i))
  -- diagonal: a prime value in `3 mod 8` has totient exactly `2 mod 8`
  have hdiagTot (i : ι) : Nat.totient (F.value i (row i)) % 8 = 2 := by
    have hprime : (F.value i (row i)).Prime := (hrow i).targetPrime
    have hmod : F.value i (row i) % 8 = 3 % 8 := (hrow i).targetMod
    rw [Nat.totient_prime hprime]
    have h1 : 1 ≤ F.value i (row i) := hprime.one_le
    omega
  -- off-diagonal: a fresh prime `≡ 1 mod 8` divides the value
  have hoffTot (i j : ι) (hji : j ≠ i) : 8 ∣ Nat.totient (F.value j (row i)) := by
    have hq := (hrow i).offPrime_prime j hji
    have hdvd : (hrow i).offPrime j hji ∣ F.value j (row i) :=
      (hrow i).offPrime_dvd j hji
    have h8 : 8 ∣ (hrow i).offPrime j hji - 1 :=
      (Nat.modEq_iff_dvd' hq.one_le).mp ((hrow i).offPrime_modEq j hji).symm
    refine h8.trans ?_
    rw [← Nat.totient_prime hq]
    exact Nat.totient_dvd_of_dvd hdvd
  have hdiv (i j : ι) : 2 ^ 1 ∣ M i j := by
    by_cases hji : j = i
    · simp only [M, hji]
      have h := hdiagTot i
      omega
    · exact dvd_trans (by norm_num) (hoffTot i j hji)
  have hdiag (i : ι) : Odd (M i i / 2 ^ 1) := by
    have := hdiagTot i
    simp only [M]
    rw [Nat.odd_iff]
    omega
  have hoff (i j : ι) (hij : i ≠ j) : Even (M i j / 2 ^ 1) := by
    obtain ⟨k, hk⟩ := hoffTot i j (Ne.symm hij)
    simp only [M]
    rw [Nat.even_iff]
    omega
  exact ⟨row, by
    have := paritySeparatedMatrix_det_ne_zero M (fun _ => 1) hdiv hdiag hoff
    simpa [M, family] using this⟩

/-- **Odd-slope affine totient independence.** -/
theorem linearIndependent_family : LinearIndependent ℚ F.family :=
  linearIndependent_of_separatedMinorCertificate F.family
    F.separatedMinorCertificate

end OddSlopeAffineFamily

end Erdos249257
