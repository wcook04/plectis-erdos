import Mathlib
import Erdos249257.CertificateKernel

/-!
# Erdős #257: the squarefree support against the block-certificate engines

For a support `A ⊆ ℕ` the Lambert rearrangement carries the value
`∑_{a ∈ A} 1/(b^a − 1)` onto the power series whose coefficient at `n` is the
divisor incidence `sc_A(n) = #{d ∣ n : d ∈ A}` — this is `Erdos249257.supportCoeff`.
The two engines in `Erdos249257.CertificateKernel` that accept an *arbitrary*
support consume block certificates for that coefficient sequence:

* `irrational_erdosSupportSeries_of_weighted_coeff_certificates`, whose first
  block is certified digitwise (`b^r ∣ sc_A(N+r)` for `1 ≤ r ≤ K`); and
* `irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates`, whose
  first block is certified in carried aggregate
  (`b^K ∣ ∑_{r ≤ K} sc_A(N+r)·b^(K−r)`), which is strictly weaker.

This file settles the squarefree support `A = {d ≥ 2 : d squarefree}` against
both, and then records — honestly — that the obstruction is a property of the
*coefficient normalisation* rather than of the support.

## What is proved

1. `squarefreeIncidence_eq`: `sc_A(n) = 2^ω(n) − 1`, hence
   (`odd_squarefreeIncidence`) odd at every `n ≥ 2`, and never zero there
   (`one_le_squarefreeIncidence`).
2. `no_carry_block_certificate`: for every **even** base `b ≥ 2` the precision
   `q = b²` admits no carry block certificate at all — no `(N, K, L, C)`.
   The argument is not merely "the opening parity fails": the parity kills every
   `K ≥ 1` (`dvd_last_of_carry_block` shows both block conditions force
   `b ∣ sc_A(N+K)`), and the *density* of the support kills `K = 0`, because
   `sc_A ≥ 1` from `n = 2` on leaves no room under the arithmetic budget.
3. `not_exists_carry_certificates_squarefreeSupport` and
   `not_exists_digitwise_certificates_squarefreeSupport`: the hypotheses of the
   two engine theorems, quoted verbatim, are false at this support.

## What the repair does

Adjoining the single element `1` to the support adds the rational `1/(b − 1)`
to the value, so it leaves the irrationality question unchanged
(`irrational_erdosSupportSeries_squarefreeSupport_iff_shifted`).  It changes the
coefficient to `2^ω(n)` (`supportCoeff_squarefreeShiftedSupport`), which is even
at every `n ≥ 2`, and it makes the full digitwise opening condition satisfiable
**for every block length** (`exists_digitwise_block_squarefreeShiftedSupport`,
by a Chinese-remainder construction).  So the parity obstruction does not
survive the shift, and no statement here should be read as saying the squarefree
support is beyond the method — only that it is beyond the method *in the
normalisation in which the coefficient is `2^ω(n) − 1`*.

Nothing here bears on the irrationality of the squarefree-support value, which
is open, and nothing here bears on universal #257.
-/

namespace ErdosProblems.Erdos257

open Finset

/-! ## The squarefree support and its divisor incidence -/

/-- The squarefree support of Erdős #257: squarefree integers `d ≥ 2`. -/
def squarefreeSupport : Set ℕ := {d : ℕ | 2 ≤ d ∧ Squarefree d}

/-- The squarefree support with the element `1` adjoined.  Since
`1/(b^1 − 1) = 1/(b − 1)` is rational, this support poses the same irrationality
question; see `irrational_erdosSupportSeries_squarefreeSupport_iff_shifted`. -/
def squarefreeShiftedSupport : Set ℕ := {d : ℕ | 1 ≤ d ∧ Squarefree d}

/-- The squarefree divisors of `n` are exactly the products of sets of its
prime factors. -/
theorem squarefreeDivisors_eq_image {n : ℕ} (hn : n ≠ 0) :
    {d ∈ n.divisors | Squarefree d}
      = n.primeFactors.powerset.image (fun s => ∏ p ∈ s, p) := by
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_image, mem_powerset]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hsq⟩
    exact ⟨d.primeFactors, Nat.primeFactors_mono hdvd hn,
      Nat.prod_primeFactors_of_squarefree hsq⟩
  · rintro ⟨s, hs, rfl⟩
    have hprime : ∀ p ∈ s, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hs hp)
    have hdvd : (∏ p ∈ s, p) ∣ n :=
      (Finset.prod_dvd_prod_of_subset _ _ _ hs).trans (Nat.prod_primeFactors_dvd n)
    refine ⟨⟨hdvd, hn⟩, ?_⟩
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun p hp => ?_)
    · intro p hp q hq hpq
      show IsRelPrime p q
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
    · exact (hprime p hp).squarefree

/-- **The squarefree divisor count.**  A nonzero `n` has exactly `2^ω(n)`
squarefree divisors, where `ω(n)` is the number of distinct prime factors. -/
theorem card_squarefreeDivisors {n : ℕ} (hn : n ≠ 0) :
    #{d ∈ n.divisors | Squarefree d} = 2 ^ n.primeFactors.card := by
  rw [squarefreeDivisors_eq_image hn, Finset.card_image_of_injOn, Finset.card_powerset]
  intro s hs t ht hst
  replace hst : (∏ p ∈ s, p) = ∏ p ∈ t, p := hst
  have hsp : ∀ p ∈ s, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_coe.mp hs) hp)
  have htp : ∀ p ∈ t, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_coe.mp ht) hp)
  rw [← Nat.primeFactors_prod hsp, ← Nat.primeFactors_prod htp, hst]

/-- The divisor incidence of the squarefree support `{d ≥ 2 : d squarefree}`:
the number of squarefree divisors of `n` other than `1`. -/
def squarefreeIncidence (n : ℕ) : ℕ := #{d ∈ n.divisors | 2 ≤ d ∧ Squarefree d}

/-- **Exact incidence of the squarefree support.**  For every `n ≥ 1`,
`sc_A(n) = 2^ω(n) − 1`. -/
theorem squarefreeIncidence_eq {n : ℕ} (hn : n ≠ 0) :
    squarefreeIncidence n = 2 ^ n.primeFactors.card - 1 := by
  have hone : {d ∈ n.divisors | Squarefree d} = insert 1 {d ∈ n.divisors | 2 ≤ d ∧ Squarefree d} := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_insert]
    constructor
    · rintro ⟨⟨hdvd, h0⟩, hsq⟩
      rcases Nat.lt_or_ge d 2 with hlt | hge
      · interval_cases d
        · exact absurd (Nat.eq_zero_of_zero_dvd hdvd) h0
        · exact Or.inl rfl
      · exact Or.inr ⟨⟨hdvd, h0⟩, hge, hsq⟩
    · rintro (rfl | ⟨hd, -, hsq⟩)
      · exact ⟨⟨one_dvd n, hn⟩, squarefree_one⟩
      · exact ⟨hd, hsq⟩
  have hnotmem : (1 : ℕ) ∉ {d ∈ n.divisors | 2 ≤ d ∧ Squarefree d} := by
    simp only [mem_filter, not_and]
    intro _ h
    omega
  have hcard := card_squarefreeDivisors hn
  rw [hone, Finset.card_insert_of_notMem hnotmem] at hcard
  unfold squarefreeIncidence
  omega

/-- **The squarefree incidence is odd at every `n ≥ 2`.**

This is what closes the parity door: the block conditions of both engines force
an even coefficient somewhere inside the first block
(`dvd_last_of_carry_block`), and no even value ever occurs. -/
theorem odd_squarefreeIncidence {n : ℕ} (hn : 2 ≤ n) :
    Odd (squarefreeIncidence n) := by
  have hn0 : n ≠ 0 := by omega
  have hpos : 0 < n.primeFactors.card := by
    rw [Finset.card_pos]
    exact (Nat.nonempty_primeFactors).mpr hn
  rw [squarefreeIncidence_eq hn0]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [hk, pow_succ]
  refine ⟨2 ^ k - 1, ?_⟩
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- **The squarefree support is dense in the coefficient sense**: every `n ≥ 2`
has at least one squarefree divisor `≥ 2`, namely any prime factor.  This is
what closes the *gap* door: the engines' other regime, `K = 0`, needs the
coefficients to be small over a long block, and here they never vanish. -/
theorem one_le_squarefreeIncidence {n : ℕ} (hn : 2 ≤ n) : 1 ≤ squarefreeIncidence n := by
  obtain ⟨k, hk⟩ := odd_squarefreeIncidence hn
  omega

/-- The shifted coefficient `2^ω(n)` never leaves the Erdős coefficient range
`1 ≤ c(n) ≤ n`, so the repair of the parity by adjoining `1` to the support
keeps the sequence admissible for the engines. -/
theorem two_pow_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card
      ≤ ∏ p ∈ n.primeFactors, p := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- The engine's coefficient at the squarefree support is exactly the incidence
computed above. -/
theorem supportCoeff_squarefreeSupport (n : ℕ) :
    Erdos249257.supportCoeff squarefreeSupport n = squarefreeIncidence n := by
  classical
  unfold Erdos249257.supportCoeff squarefreeIncidence
  congr 1
  refine Finset.filter_congr fun d _ => ?_
  simp only [squarefreeSupport, Set.mem_setOf_eq]

/-! ## No block certificate exists at the squarefree support -/

/-- **The parity kernel of both block conditions.**  A first block certified in
carried aggregate — the weaker of the two conditions — still forces the base to
divide the coefficient at the *last* position of the block.  Every other term of
the carry sum carries a positive power of `b`. -/
theorem dvd_last_of_carry_block {b N K : ℕ} {c : ℕ → ℕ} (hK : 1 ≤ K)
    (h : b ^ K ∣ ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r)) :
    b ∣ c (N + K) := by
  have hS : b ∣ ∑ r ∈ Finset.Icc 1 K, c (N + r) * b ^ (K - r) :=
    (dvd_pow_self b (by omega : K ≠ 0)).trans h
  have hins : Finset.Icc 1 K = insert K (Finset.Icc 1 (K - 1)) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : K ∉ Finset.Icc 1 (K - 1) := by
    simp only [Finset.mem_Icc]
    omega
  rw [hins, Finset.sum_insert hnot, Nat.sub_self, pow_zero, mul_one] at hS
  have hrest : b ∣ ∑ r ∈ Finset.Icc 1 (K - 1), c (N + r) * b ^ (K - r) := by
    refine Finset.dvd_sum fun r hr => ?_
    have hr' := Finset.mem_Icc.mp hr
    exact Dvd.dvd.mul_left (dvd_pow_self b (by omega : K - r ≠ 0)) _
  simpa using Nat.dvd_sub hS hrest

/-- **No carry block certificate exists at the squarefree support.**

For every even base `b ≥ 2` the single precision `q = b²` already admits no
tuple `(N, K, L, C)` satisfying the carry-aware block certificate.  Two
independent facts about the support are used, one for each regime the schema
allows:

* `K ≥ 1` is impossible by parity — `dvd_last_of_carry_block` forces
  `b ∣ sc_A(N+K)`, and `sc_A` is odd at every argument `≥ 2` while `b` is even,
  so the block would have to reach the single position `n = 1`;
* `K ≤ 1` is then impossible by density — the coefficient at `N + 2` is at least
  `1`, so the middle block alone spends the whole budget `b^L`.

The obstruction is therefore uniform in the block position, and quantitative:
it is not that a search has not gone far enough. -/
theorem no_carry_block_certificate {b N K L C : ℕ}
    (hb : 2 ≤ b) (hbeven : 2 ∣ b)
    (hcarry : b ^ K ∣ ∑ r ∈ Finset.Icc 1 K, squarefreeIncidence (N + r) * b ^ (K - r))
    (hmiddle : ∑ r ∈ Finset.Icc (K + 1) L, squarefreeIncidence (N + r) * b ^ (L - r) ≤ C)
    (harith : b ^ 2 * (C + (N + L + 2)) < b ^ L) : False := by
  -- Step 1: parity bounds the certified block length by one.
  have hK1 : K ≤ 1 := by
    by_contra hK
    have hK2 : 2 ≤ K := by omega
    have hdvd : b ∣ squarefreeIncidence (N + K) := dvd_last_of_carry_block (by omega) hcarry
    have h2 : (2 : ℕ) ∣ squarefreeIncidence (N + K) := hbeven.trans hdvd
    have hodd : Odd (squarefreeIncidence (N + K)) := odd_squarefreeIncidence (by omega)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hb0 : 0 < b := by omega
  rcases Nat.lt_or_ge L 2 with hL | hL
  · -- Short blocks: the budget `b^L ≤ b` cannot even cover the constant term.
    have h1 : b ^ L ≤ b := by
      interval_cases L
      · simpa using (by omega : (1 : ℕ) ≤ b)
      · simp
    have h2 : 2 * b ^ 2 ≤ b ^ 2 * (C + (N + L + 2)) := by
      calc 2 * b ^ 2 = b ^ 2 * 2 := by ring
        _ ≤ b ^ 2 * (C + (N + L + 2)) := Nat.mul_le_mul_left _ (by omega)
    have hsq : b ^ 2 = b * b := by ring
    have h3 : b < 2 * b ^ 2 := by rw [hsq]; nlinarith
    omega
  · -- Long blocks: the coefficient at `N + 2` alone exhausts the budget.
    have hmem : 2 ∈ Finset.Icc (K + 1) L := Finset.mem_Icc.mpr ⟨by omega, hL⟩
    have hterm : squarefreeIncidence (N + 2) * b ^ (L - 2)
        ≤ ∑ r ∈ Finset.Icc (K + 1) L, squarefreeIncidence (N + r) * b ^ (L - r) :=
      Finset.single_le_sum
        (f := fun r => squarefreeIncidence (N + r) * b ^ (L - r))
        (fun i _ => Nat.zero_le _) hmem
    have hone : 0 < squarefreeIncidence (N + 2) := one_le_squarefreeIncidence (by omega)
    have hlow : b ^ (L - 2) ≤ C := by
      have hmul : b ^ (L - 2) ≤ squarefreeIncidence (N + 2) * b ^ (L - 2) :=
        Nat.le_mul_of_pos_left _ hone
      omega
    have hpow : b ^ 2 * b ^ (L - 2) = b ^ L := by
      rw [← pow_add]
      congr 1
      omega
    have hbig : b ^ L ≤ b ^ 2 * (C + (N + L + 2)) := by
      calc b ^ L = b ^ 2 * b ^ (L - 2) := hpow.symm
        _ ≤ b ^ 2 * C := Nat.mul_le_mul_left _ hlow
        _ ≤ b ^ 2 * (C + (N + L + 2)) := Nat.mul_le_mul_left _ (by omega)
    omega

/-- **The carry-aware engine has no instance at the squarefree support.**  The
statement quotes the hypothesis of
`Erdos249257.irrational_erdosSupportSeries_of_weighted_coeff_carry_certificates`
verbatim, at the squarefree support, and refutes it for every even base. -/
theorem not_exists_carry_certificates_squarefreeSupport {b : ℕ} (hb : 2 ≤ b) (hbeven : 2 ∣ b) :
    ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
          Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (K - r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L,
          Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < Erdos249257.supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) := by
  intro hcert
  obtain ⟨N, K, L, C, -, hcarry, hmiddle, -, harith⟩ := hcert (b ^ 2) (by positivity)
  simp only [supportCoeff_squarefreeSupport] at hcarry hmiddle
  exact no_carry_block_certificate hb hbeven hcarry hmiddle harith

/-- **The digitwise engine has no instance at the squarefree support.**  The
statement quotes the hypothesis of
`Erdos249257.irrational_erdosSupportSeries_of_weighted_coeff_certificates`
verbatim.  It is refuted through the carry form, using the development's own
proof that the carry interface subsumes the digitwise one. -/
theorem not_exists_digitwise_certificates_squarefreeSupport
    {b : ℕ} (hb : 2 ≤ b) (hbeven : 2 ∣ b) :
    ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K,
          b ^ r ∣ Erdos249257.supportCoeff squarefreeSupport (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L,
          Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < Erdos249257.supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) := by
  intro hcert
  refine not_exists_carry_certificates_squarefreeSupport hb hbeven fun q hq => ?_
  obtain ⟨N, K, L, C, hKL, hblock, hmiddle, hpos, harith⟩ := hcert q hq
  exact ⟨N, K, L, C, hKL,
    Erdos249257.carry_block_dvd_of_digitwise_blocks b N K _ hblock, hmiddle, hpos, harith⟩

/-! ## The repair: adjoining `1` to the support

The obstruction above is stated about the coefficient sequence `2^ω(n) − 1`.
The obvious objection is that the `−1` is a normalisation choice, and the
objection is correct.  This section proves it. -/

/-- The shifted support has coefficient `2^ω(n)`. -/
theorem supportCoeff_squarefreeShiftedSupport {n : ℕ} (hn : n ≠ 0) :
    Erdos249257.supportCoeff squarefreeShiftedSupport n = 2 ^ n.primeFactors.card := by
  classical
  have hfilter : Erdos249257.supportCoeff squarefreeShiftedSupport n
      = #{d ∈ n.divisors | Squarefree d} := by
    unfold Erdos249257.supportCoeff
    congr 1
    refine Finset.filter_congr fun d hd => ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp only [squarefreeShiftedSupport, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨by omega, h⟩
  rw [hfilter, card_squarefreeDivisors hn]

/-- **The shift is free.**  Adjoining `1` to the squarefree support changes the
value by `1/(b − 1)`, a rational, so the two supports pose the same
irrationality question.  Both directions go through the development's own
finite-prefix invariance theorems. -/
theorem irrational_erdosSupportSeries_squarefreeSupport_iff_shifted (b : ℕ) (hb : 2 ≤ b) :
    Irrational (Erdos249257.erdosSupportSeries b squarefreeSupport)
      ↔ Irrational (Erdos249257.erdosSupportSeries b squarefreeShiftedSupport) := by
  have hset : {n : ℕ | n ∈ squarefreeShiftedSupport ∧ 1 < n} = squarefreeSupport := by
    ext n
    simp only [Set.mem_setOf_eq, squarefreeShiftedSupport, squarefreeSupport]
    constructor
    · rintro ⟨⟨-, hsq⟩, h⟩
      exact ⟨by omega, hsq⟩
    · rintro ⟨h2, hsq⟩
      exact ⟨⟨by omega, hsq⟩, by omega⟩
  constructor
  · intro h
    refine Erdos249257.irrational_erdosSupportSeries_of_tail b squarefreeShiftedSupport hb 1 ?_
    rw [hset]
    exact h
  · intro h
    have htail :=
      Erdos249257.irrational_erdosSupportSeries_tail_of_irrational b squarefreeShiftedSupport hb 1 h
    rwa [hset] at htail

/-! ### Arbitrarily long divisible blocks for the shifted coefficient

The digitwise opening condition at base `2` reads `2^r ∣ 2^ω(N+r)`, that is
`ω(N+r) ≥ r` for `1 ≤ r ≤ K`.  A Chinese-remainder construction supplies such
an `N` for every `K`: reserve `r` fresh primes for the shift `r` and force their
product to divide `N + r`. -/

/-- Triangular offset: where block `r` starts in the enumeration of the primes. -/
def primeBlockStart (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, i

theorem primeBlockStart_succ (r : ℕ) :
    primeBlockStart (r + 1) = primeBlockStart r + r :=
  Finset.sum_range_succ _ _

theorem primeBlockStart_mono {r r' : ℕ} (h : r ≤ r') :
    primeBlockStart r ≤ primeBlockStart r' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- The block of prime indices reserved for the shift `r`. -/
def primeIndexBlock (r : ℕ) : Finset ℕ :=
  Finset.Ico (primeBlockStart r) (primeBlockStart r + r)

theorem primeIndexBlock_disjoint {r r' : ℕ} (h : r ≠ r') :
    Disjoint (primeIndexBlock r) (primeIndexBlock r') := by
  -- symmetric in `r, r'`, so it suffices to treat `r < r'`
  have key : ∀ s t : ℕ, s < t → Disjoint (primeIndexBlock s) (primeIndexBlock t) := by
    intro s t hst
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := Finset.mem_Ico.mp hx
    have h2 := Finset.mem_Ico.mp hx'
    have hchain : primeBlockStart s + s ≤ primeBlockStart t := by
      rw [← primeBlockStart_succ s]
      exact primeBlockStart_mono (by omega)
    omega
  rcases Nat.lt_or_ge r r' with hlt | hge
  · exact key r r' hlt
  · exact (key r' r (by omega)).symm

theorem card_primeIndexBlock (r : ℕ) : (primeIndexBlock r).card = r := by
  simp [primeIndexBlock]

/-- The `r` distinct primes reserved for the shift `r`. -/
noncomputable def primeBlock (r : ℕ) : Finset ℕ :=
  (primeIndexBlock r).image (Nat.nth Nat.Prime)

theorem prime_of_mem_primeBlock {r p : ℕ} (hp : p ∈ primeBlock r) : Nat.Prime p := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  exact Nat.prime_nth_prime i

theorem card_primeBlock (r : ℕ) : (primeBlock r).card = r := by
  rw [primeBlock,
    Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOf_prime),
    card_primeIndexBlock]

theorem primeBlock_disjoint {r r' : ℕ} (h : r ≠ r') :
    Disjoint (primeBlock r) (primeBlock r') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp hp
  obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp hp'
  have hij : i = j :=
    Nat.nth_injective Nat.infinite_setOf_prime (hpi.trans hpj.symm)
  subst hij
  exact (Finset.disjoint_left.mp (primeIndexBlock_disjoint h) hi) hj

/-- The modulus reserved for the shift `r`: the product of its `r` primes. -/
noncomputable def primeBlockModulus (r : ℕ) : ℕ := ∏ p ∈ primeBlock r, p

theorem primeBlockModulus_ne_zero (r : ℕ) : primeBlockModulus r ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  exact (prime_of_mem_primeBlock hp).ne_zero

theorem coprime_primeBlockModulus {r r' : ℕ} (h : r ≠ r') :
    Nat.Coprime (primeBlockModulus r) (primeBlockModulus r') := by
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun p' hp' => ?_
  have hpp := prime_of_mem_primeBlock hp
  have hpp' := prime_of_mem_primeBlock hp'
  refine (Nat.coprime_primes hpp hpp').mpr fun hEq => ?_
  subst hEq
  exact (Finset.disjoint_left.mp (primeBlock_disjoint h) hp) hp'

/-- **Arbitrarily long prescribed `ω`-blocks.**  For every `K` there is a
positive `N` with `ω(N + r) ≥ r` for every `1 ≤ r ≤ K`.  Chinese remainder over
disjoint blocks of primes. -/
theorem exists_omega_ge_block (K : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r ∈ Finset.Icc 1 K, r ≤ (N + r).primeFactors.card := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    Nat.chineseRemainderOfFinset (fun r => r * (primeBlockModulus r - 1)) primeBlockModulus
      (Finset.Icc 1 K) (fun r _ => primeBlockModulus_ne_zero r)
      (fun r _ r' _ hne => coprime_primeBlockModulus hne)
  set M : ℕ := ∏ r ∈ Finset.Icc 1 K, primeBlockModulus r with hM
  have hMpos : 0 < M := by
    refine Finset.prod_pos fun r _ => ?_
    exact Nat.pos_of_ne_zero (primeBlockModulus_ne_zero r)
  refine ⟨N₀ + M, by omega, fun r hr => ?_⟩
  have hmr0 : primeBlockModulus r ≠ 0 := primeBlockModulus_ne_zero r
  -- the reserved modulus divides `N + r`
  have hshift : primeBlockModulus r ∣ N₀ + r := by
    have h1 : N₀ ≡ r * (primeBlockModulus r - 1) [MOD primeBlockModulus r] := hN₀ r hr
    have h2 : N₀ + r ≡ r * (primeBlockModulus r - 1) + r [MOD primeBlockModulus r] :=
      h1.add_right r
    have h3 : r * (primeBlockModulus r - 1) + r = r * primeBlockModulus r := by
      have hsucc : primeBlockModulus r - 1 + 1 = primeBlockModulus r :=
        Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hmr0)
      calc r * (primeBlockModulus r - 1) + r = r * (primeBlockModulus r - 1 + 1) := by ring
        _ = r * primeBlockModulus r := by rw [hsucc]
    rw [h3] at h2
    have h4 : r * primeBlockModulus r ≡ 0 [MOD primeBlockModulus r] :=
      (Nat.modEq_zero_iff_dvd).mpr ⟨r, by ring⟩
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans h4)
  have hdvdM : primeBlockModulus r ∣ M := Finset.dvd_prod_of_mem _ hr
  have hdvd : primeBlockModulus r ∣ N₀ + M + r := by
    have : N₀ + M + r = (N₀ + r) + M := by ring
    rw [this]
    exact Nat.dvd_add hshift hdvdM
  -- so all `r` reserved primes are prime factors of `N + r`
  have hsub : primeBlock r ⊆ (N₀ + M + r).primeFactors := by
    intro p hp
    refine Nat.mem_primeFactors.mpr ⟨prime_of_mem_primeBlock hp, ?_, by omega⟩
    exact (Finset.dvd_prod_of_mem _ hp).trans hdvd
  calc r = (primeBlock r).card := (card_primeBlock r).symm
    _ ≤ (N₀ + M + r).primeFactors.card := Finset.card_le_card hsub

/-- **The parity obstruction does not survive the shift.**  For every block
length `K` the shifted support admits a position `N` at which the *full*
digitwise opening condition of the base-`2` engine holds — the condition whose
failure at the unshifted support is `no_carry_block_certificate`. -/
theorem exists_digitwise_block_squarefreeShiftedSupport (K : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r ∈ Finset.Icc 1 K,
      2 ^ r ∣ Erdos249257.supportCoeff squarefreeShiftedSupport (N + r) := by
  obtain ⟨N, hN, h⟩ := exists_omega_ge_block K
  refine ⟨N, hN, fun r hr => ?_⟩
  rw [supportCoeff_squarefreeShiftedSupport (by omega : N + r ≠ 0)]
  exact pow_dvd_pow 2 (h r hr)

end ErdosProblems.Erdos257
