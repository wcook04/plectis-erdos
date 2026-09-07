import Erdos257PeriodNoncollapse.SupportDilationDifferences

/-!
# Erdős #257: cofinal denominator-21 repair at multiples of 120

The exact computation at `1 / 21` isolates the candidate

`Q_(120 k) ≤ Q_(120 k - 1)`.

This module records its shortest checked consumer.  A non-rise at one rank
already forces a linear bound there: the defect recurrence and the universal
bound `supportCoeff A n ≤ n` give `Q_n ≤ n`.  Multiples of `120` are
cofinal, so these linear returns feed the existing tempered-carry endpoint.

The all-depth non-rise and primorial-repair statements formalized here are now
known to be false for the canonical orbit.  The exact identities and
conditional consumers are retained because they expose the failure coordinate;
nothing here proves membership or settles Erdős #257.
-/

namespace ErdosProblems.Erdos257

open Set
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.SupportDilationDifferences

/-- The selected divisors of one rank, exposed as a finite set so the
three-prime union can be counted without natural-number subtraction. -/
private noncomputable def selectedDivisors (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  letI := Classical.decPred fun d : ℕ ↦ d ∈ A
  n.divisors.filter fun d ↦ d ∈ A

private theorem selectedDivisors_card (A : Set ℕ) (n : ℕ) :
    (selectedDivisors A n).card = supportCoeff A n := by
  classical
  unfold selectedDivisors
  exact (supportCoeff_eq_card_filter A n).symm

private theorem mem_twentyOnePrefixRat_iff_real_support
    {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    d ∈ greedyMersennePrefixRat (1 / 21 : ℚ) n ↔
      d ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
  classical
  unfold greedyMersennePrefixRat
  constructor
  · intro hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨-, htake⟩ := Finset.mem_filter.mp hj
    have htakeR :=
      (rational_greedy_take_iff_real (1 / 21 : ℚ) j).1 htake
    norm_num at htakeR
    exact (succ_mem_greedyMersenneSupport_iff (1 / 21 : ℝ) j).2 htakeR
  · intro hd
    refine Finset.mem_image.mpr ⟨d - 1, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    apply (rational_greedy_take_iff_real (1 / 21 : ℚ) (d - 1)).2
    have htakeR :=
      (succ_mem_greedyMersenneSupport_iff (1 / 21 : ℝ) (d - 1)).1
        (by simpa only [Nat.sub_add_cancel hd1] using hd)
    norm_num at htakeR ⊢
    exact htakeR

private theorem selectedDivisors_mono_of_dvd
    (A : Set ℕ) {a n : ℕ} (han : a ∣ n) (hn : 0 < n) :
    selectedDivisors A a ⊆ selectedDivisors A n := by
  classical
  intro d hd
  unfold selectedDivisors at hd ⊢
  rcases Finset.mem_filter.mp hd with ⟨hda, hdA⟩
  rcases Nat.mem_divisors.mp hda with ⟨hda, -⟩
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨hda.trans han, hn.ne'⟩, hdA⟩

private theorem selectedDivisors_inter
    (A : Set ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    selectedDivisors A a ∩ selectedDivisors A b =
      selectedDivisors A (Nat.gcd a b) := by
  classical
  ext d
  unfold selectedDivisors
  simp only [Finset.mem_inter, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨hda, -⟩, hdA⟩, ⟨⟨hdb, -⟩, -⟩⟩
    exact ⟨⟨Nat.dvd_gcd hda hdb, (Nat.gcd_pos_of_pos_left b ha).ne'⟩, hdA⟩
  · rintro ⟨⟨hdg, -⟩, hdA⟩
    exact
      ⟨⟨⟨hdg.trans (Nat.gcd_dvd_left a b), ha.ne'⟩, hdA⟩,
        ⟨⟨hdg.trans (Nat.gcd_dvd_right a b), hb.ne'⟩, hdA⟩⟩

/-- Subtraction-free inclusion-exclusion for three selected-divisor columns.
This is the abstract seven-column identity; the modulus-`120` specialization
below turns its gcd columns into division by `6,10,15,30`. -/
private theorem selectedDivisors_union_three_card_identity
    (A : Set ℕ) {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (((selectedDivisors A a ∪ selectedDivisors A b) ∪
          selectedDivisors A c).card +
        supportCoeff A (Nat.gcd a b) +
        supportCoeff A (Nat.gcd a c) +
        supportCoeff A (Nat.gcd b c) =
      supportCoeff A a + supportCoeff A b + supportCoeff A c +
        supportCoeff A (Nat.gcd (Nat.gcd a b) c)) := by
  classical
  let X := selectedDivisors A a
  let Y := selectedDivisors A b
  let Z := selectedDivisors A c
  have hXY : X ∩ Y = selectedDivisors A (Nat.gcd a b) := by
    exact selectedDivisors_inter A ha hb
  have hXZ : X ∩ Z = selectedDivisors A (Nat.gcd a c) := by
    exact selectedDivisors_inter A ha hc
  have hYZ : Y ∩ Z = selectedDivisors A (Nat.gcd b c) := by
    exact selectedDivisors_inter A hb hc
  have hgcd : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hXYZ : X ∩ Y ∩ Z =
      selectedDivisors A (Nat.gcd (Nat.gcd a b) c) := by
    rw [hXY]
    exact selectedDivisors_inter A hgcd hc
  have hdistrib : (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z) := by
    ext d
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hinter : (X ∩ Z) ∩ (Y ∩ Z) = X ∩ Y ∩ Z := by
    ext d
    simp only [Finset.mem_inter]
    tauto
  have hXYcard := Finset.card_union_add_card_inter X Y
  have hXYZcard := Finset.card_union_add_card_inter (X ∪ Y) Z
  have hpairCard := Finset.card_union_add_card_inter (X ∩ Z) (Y ∩ Z)
  rw [hdistrib] at hXYZcard
  rw [hinter] at hpairCard
  have hcount :
      ((X ∪ Y) ∪ Z).card + (X ∩ Y).card + (X ∩ Z).card +
          (Y ∩ Z).card =
        X.card + Y.card + Z.card + (X ∩ Y ∩ Z).card := by
    omega
  rw [hXYZ, hXY, hXZ, hYZ] at hcount
  simpa only [X, Y, Z, selectedDivisors_card] using hcount

/-- The causal three-prime load.  It counts selected ranks which divide at
least one of `n / 2`, `n / 3`, or `n / 5`; every such decision was made by
rank `n / 2`. -/
noncomputable def twentyOnePrimorialUnionLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  ((selectedDivisors A (n / 2) ∪ selectedDivisors A (n / 3)) ∪
      selectedDivisors A (n / 5)).card

/-- Exact finite base socket for the prime-column normal form.  The value is
native-certified from the computable rational greedy prefix through rank
`240`, then transported to the real greedy support decision by decision. -/
theorem twentyOnePrimorialUnionLoad_240 :
    twentyOnePrimorialUnionLoad 240 = 7 := by
  classical
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  let P : Set ℕ := ↑(greedyMersennePrefixRat (1 / 21 : ℚ) 240)
  have hselected (n : ℕ) (hn : 0 < n) (hn240 : n ≤ 240) :
      selectedDivisors A n = selectedDivisors P n := by
    ext d
    unfold selectedDivisors
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hddiv, hdA⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd240 : d ≤ 240 := (Nat.le_of_dvd hn hdvd).trans hn240
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (1 / 21 : ℚ) 240
        exact (mem_twentyOnePrefixRat_iff_real_support hdpos hd240).2 hdA⟩
    · rintro ⟨hddiv, hdP⟩
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hddiv
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
      have hd240 : d ≤ 240 := (Nat.le_of_dvd hn hdvd).trans hn240
      exact ⟨hddiv, by
        change d ∈ greedyMersennePrefixRat (1 / 21 : ℚ) 240 at hdP
        exact (mem_twentyOnePrefixRat_iff_real_support hdpos hd240).1 hdP⟩
  change ((selectedDivisors A (240 / 2) ∪ selectedDivisors A (240 / 3)) ∪
      selectedDivisors A (240 / 5)).card = 7
  norm_num only [Nat.reduceDiv]
  rw [hselected 120 (by norm_num) (by norm_num),
    hselected 80 (by norm_num) (by norm_num),
    hselected 48 (by norm_num) (by norm_num)]
  simp only [selectedDivisors, P, Finset.mem_coe]
  native_decide

/-- Exact seven-column form of the causal union at a positive multiple of
`120`.  It is stated without subtraction so it remains an identity in `ℕ`. -/
theorem twentyOnePrimorialUnionLoad_sevenColumn (k : ℕ) :
    let n := 120 * (k + 1)
    let A := greedyMersenneSupport (1 / 21 : ℝ)
    twentyOnePrimorialUnionLoad n + supportCoeff A (n / 6) +
          supportCoeff A (n / 10) + supportCoeff A (n / 15) =
      supportCoeff A (n / 2) + supportCoeff A (n / 3) +
          supportCoeff A (n / 5) + supportCoeff A (n / 30) := by
  dsimp only
  let m := k + 1
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  have hm : 0 < m := by simp [m]
  have h2 : 120 * (k + 1) / 2 = 60 * m := by
    dsimp [m]
    omega
  have h3 : 120 * (k + 1) / 3 = 40 * m := by
    dsimp [m]
    omega
  have h5 : 120 * (k + 1) / 5 = 24 * m := by
    dsimp [m]
    omega
  have h6 : 120 * (k + 1) / 6 = 20 * m := by
    dsimp [m]
    omega
  have h10 : 120 * (k + 1) / 10 = 12 * m := by
    dsimp [m]
    omega
  have h15 : 120 * (k + 1) / 15 = 8 * m := by
    dsimp [m]
    omega
  have h30 : 120 * (k + 1) / 30 = 4 * m := by
    dsimp [m]
    omega
  have h := selectedDivisors_union_three_card_identity A
    (a := 60 * m) (b := 40 * m) (c := 24 * m)
    (by positivity) (by positivity) (by positivity)
  dsimp [twentyOnePrimorialUnionLoad]
  rw [h2, h3, h5, h6, h10, h15, h30]
  norm_num [Nat.gcd_mul_right] at h
  simpa only [A, Finset.union_assoc] using h

/-- At a positive multiple of `30`, the primorial union counts only genuine
selected divisors of the current rank. -/
theorem twentyOnePrimorialUnionLoad_le_supportCoeff
    {n : ℕ} (hn : 0 < n) (h30 : 30 ∣ n) :
    twentyOnePrimorialUnionLoad n ≤
      supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) n := by
  classical
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  have h2 : 2 ∣ n := (show 2 ∣ 30 by norm_num).trans h30
  have h3 : 3 ∣ n := (show 3 ∣ 30 by norm_num).trans h30
  have h5 : 5 ∣ n := (show 5 ∣ 30 by norm_num).trans h30
  have hs2 : selectedDivisors A (n / 2) ⊆ selectedDivisors A n :=
    selectedDivisors_mono_of_dvd A (Nat.div_dvd_of_dvd h2) hn
  have hs3 : selectedDivisors A (n / 3) ⊆ selectedDivisors A n :=
    selectedDivisors_mono_of_dvd A (Nat.div_dvd_of_dvd h3) hn
  have hs5 : selectedDivisors A (n / 5) ⊆ selectedDivisors A n :=
    selectedDivisors_mono_of_dvd A (Nat.div_dvd_of_dvd h5) hn
  rw [← selectedDivisors_card A n]
  apply Finset.card_le_card
  intro d hd
  rcases Finset.mem_union.mp hd with hd | hd
  · rcases Finset.mem_union.mp hd with hd | hd
    · exact hs2 hd
    · exact hs3 hd
  · exact hs5 hd

/-- The selected divisors appearing for the first time after doubling a
rank.  This is the source-owned excess-multiplicity layer in the doubled
primorial repair: no subtraction is exposed in later natural-number
identities. -/
noncomputable def twentyOneTopTwoAdicLayerLoad (n : ℕ) : ℕ :=
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  (selectedDivisors A (2 * n) \ selectedDivisors A n).card

/-- At a positive rank, the full divisor load after doubling splits into
the old divisor load and the genuinely new top `2`-adic layer. -/
theorem twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
    {n : ℕ} (hn : 0 < n) :
    supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (2 * n) =
      supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) n +
        twentyOneTopTwoAdicLayerLoad n := by
  classical
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  have hsubset : selectedDivisors A n ⊆ selectedDivisors A (2 * n) := by
    apply selectedDivisors_mono_of_dvd A
    · exact ⟨2, by omega⟩
    · positivity
  have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
  rw [selectedDivisors_card A n, selectedDivisors_card A (2 * n)] at hsplit
  change supportCoeff A (2 * n) = supportCoeff A n +
    (selectedDivisors A (2 * n) \ selectedDivisors A n).card
  omega

/-- On the doubled modulus-`120` rows, the seven-column union is exactly the
old midpoint load plus a signed inclusion-exclusion of three new `2`-adic
layers.  This is the excess-multiplicity normal form suggested by the
modulus-`240` computation. -/
theorem twentyOnePrimorialUnionLoad_multiple240_topTwoAdicLayer (k : ℕ) :
    let m := k + 1
    let A := greedyMersenneSupport (1 / 21 : ℝ)
    twentyOnePrimorialUnionLoad (240 * m) +
          twentyOneTopTwoAdicLayerLoad (8 * m) =
      supportCoeff A (120 * m) +
        twentyOneTopTwoAdicLayerLoad (40 * m) +
          twentyOneTopTwoAdicLayerLoad (24 * m) := by
  dsimp only
  let m := k + 1
  have hm : 0 < m := by simp [m]
  have hseven :
      twentyOnePrimorialUnionLoad (240 * m) +
            supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (40 * m) +
            supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (24 * m) +
            supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (16 * m) =
        supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (120 * m) +
            supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (80 * m) +
            supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (48 * m) +
            supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (8 * m) := by
    have hraw := twentyOnePrimorialUnionLoad_sevenColumn (2 * k + 1)
    dsimp only at hraw
    have h0 : 120 * (2 * k + 1 + 1) = 240 * m := by
      dsimp [m]
      omega
    have h2 : 240 * m / 2 = 120 * m := by omega
    have h3 : 240 * m / 3 = 80 * m := by omega
    have h5 : 240 * m / 5 = 48 * m := by omega
    have h6 : 240 * m / 6 = 40 * m := by omega
    have h10 : 240 * m / 10 = 24 * m := by omega
    have h15 : 240 * m / 15 = 16 * m := by omega
    have h30 : 240 * m / 30 = 8 * m := by omega
    rw [h0] at hraw
    rw [h2, h3, h5, h6, h10, h15, h30] at hraw
    exact hraw
  have h40 :
      supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (80 * m) =
        supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (40 * m) +
        twentyOneTopTwoAdicLayerLoad (40 * m) := by
    convert twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
      (n := 40 * m) (by positivity) using 1 <;> ring_nf
  have h24 :
      supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (48 * m) =
        supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (24 * m) +
        twentyOneTopTwoAdicLayerLoad (24 * m) := by
    convert twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
      (n := 24 * m) (by positivity) using 1 <;> ring_nf
  have h8 :
      supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (16 * m) =
        supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (8 * m) +
        twentyOneTopTwoAdicLayerLoad (8 * m) := by
    convert twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
      (n := 8 * m) (by positivity) using 1 <;> ring_nf
  rw [h40, h24, h8] at hseven
  have hresult :
      twentyOnePrimorialUnionLoad (240 * m) +
            twentyOneTopTwoAdicLayerLoad (8 * m) =
        supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (120 * m) +
          twentyOneTopTwoAdicLayerLoad (40 * m) +
            twentyOneTopTwoAdicLayerLoad (24 * m) := by
    omega
  simpa only [m] using hresult

/-- The denominator-`21` baseline bit immediately before every positive
multiple of `120` is one. -/
theorem twentyOneFloorBit_pred_multiple120 (k : ℕ) :
    twentyOneFloorBit (120 * (k + 1) - 1) = 1 := by
  let t := 20 * (k + 1) - 1
  have hexp : 120 * (k + 1) - 1 = 6 * t + 5 := by
    dsimp [t]
    omega
  have hbase : 2 ^ 6 ≡ 1 [MOD 21] := by
    norm_num [Nat.ModEq]
  have hfive : 2 ^ 5 ≡ 11 [MOD 21] := by
    norm_num [Nat.ModEq]
  have hpow : (2 ^ 6) ^ t ≡ 1 ^ t [MOD 21] := hbase.pow t
  have hprod : (2 ^ 6) ^ t * 2 ^ 5 ≡ 1 ^ t * 11 [MOD 21] :=
    hpow.mul hfive
  have hmod : 2 ^ (120 * (k + 1) - 1) % 21 = 11 := by
    change 2 ^ (120 * (k + 1) - 1) ≡ 11 [MOD 21]
    rw [hexp, pow_add, pow_mul]
    simpa using hprod
  rw [twentyOneFloorBit_eq_two_mul_mod_div, hmod]
  norm_num

/-- The source-current cofinal repair candidate.  The positive shift avoids
the degenerate row zero while retaining a literal all-`k` statement. -/
def TwentyOneMultiple120DefectNonrise : Prop :=
  ∀ k : ℕ,
    twentyOneGreedyDefect (120 * (k + 1)) ≤
      twentyOneGreedyDefect (120 * (k + 1) - 1)

/-- The exact finite producer observed in the canonical orbit.  This is
`PU120`: the past-owned `{2,3,5}` divisor union pays the previous defect plus
the one periodic baseline bit. -/
def TwentyOneMultiple120PrimorialRepair : Prop :=
  ∀ k : ℕ,
    twentyOneGreedyDefect (120 * (k + 1) - 1) + 1 ≤
      twentyOnePrimorialUnionLoad (120 * (k + 1))

/-- The weaker cofinal producer selected by the exact doubled-row audit.
Only multiples of `240` are required, while the observed inequality has one
additional unit of slack. -/
def TwentyOneMultiple240PrimorialRepairSlack : Prop :=
  ∀ k : ℕ,
    twentyOneGreedyDefect (240 * (k + 1) - 1) + 2 ≤
      twentyOnePrimorialUnionLoad (240 * (k + 1))

/-! ## Coupled factor descent for the doubled repair

The doubled-layer identity naturally separates a past-owned payment from a
live debt.  Keeping the debt in the comparison is essential: static descent
of the primorial margin is false. -/

/-- The three positive terms on the right side of the doubled-layer identity.
Every selected decision counted here was made by rank `120 * m`. -/
noncomputable def twentyOneDoubledRepairPayment (m : ℕ) : ℕ :=
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  supportCoeff A (120 * m) + twentyOneTopTwoAdicLayerLoad (40 * m) +
    twentyOneTopTwoAdicLayerLoad (24 * m)

/-- The live defect together with the layer cancelled from the left side of
the doubled-layer identity. -/
noncomputable def twentyOneDoubledRepairDebt (m : ℕ) : ℕ :=
  twentyOneGreedyDefect (240 * m - 1) +
    twentyOneTopTwoAdicLayerLoad (8 * m)

/-! ## Prime-column normal form

For a prime cofactor `p > 5`, every divisor of the fixed columns
`120`, `80`, and `48` is coprime to `p`.  The support coefficient at `p*c`
therefore splits into the old coefficient at `c` and the coefficient of the
support pulled back by `p`.  Inclusion-exclusion packages the entire moving
part into one finite union. -/

/-- The fixed finite column seen after pulling the actual support back through
multiplication by `p`.  Its possible ranks are exactly the divisors of `120`,
`80`, or `48` (equivalently, the divisors of `120` together with
`16`, `48`, and `80`). -/
noncomputable def twentyOnePrimePullbackColumnLoad (p : ℕ) : ℕ :=
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  let B := supportPullback p A
  ((selectedDivisors B 120 ∪ selectedDivisors B 80) ∪
      selectedDivisors B 48).card

private theorem fixedColumn_coprime_of_prime_gt_five
    {p c : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hc : c ∣ 240) :
    c.Coprime p := by
  have hp2 : p.Coprime 2 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp3 : p.Coprime 3 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp5' : p.Coprime 5 :=
    (Nat.coprime_primes hp (by norm_num)).2 (by omega)
  have hp240' : p.Coprime ((2 ^ 4) * 3 * 5) :=
    ((Nat.Coprime.pow_right 4 hp2).mul_right hp3).mul_right hp5'
  have h240p : (240 : ℕ).Coprime p := by
    have := hp240'.symm
    norm_num at this ⊢
    exact this
  exact Nat.Coprime.of_dvd_left hc h240p

/-- Exact prime-column cancellation.  On prime cofactors above `5`, the
payment gained from the pulled-back `120/80/48` columns consists of the
literal finite union plus the pulled-back top `2`-adic layer.  That layer is
also exactly the increment in the debt term, so the subtraction-free identity
below cancels it without any estimate. -/
theorem twentyOneDoubledRepairPayment_primeColumn
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    twentyOneDoubledRepairPayment p +
        twentyOneTopTwoAdicLayerLoad 8 =
      twentyOneDoubledRepairPayment 1 +
        twentyOnePrimePullbackColumnLoad p +
          twentyOneTopTwoAdicLayerLoad (8 * p) := by
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  let B := supportPullback p A
  have hcop (c : ℕ) (hc : c ∣ 240) : c.Coprime p :=
    fixedColumn_coprime_of_prime_gt_five hp hp5 hc
  have h120 : supportCoeff A (120 * p) =
      supportCoeff A 120 + supportCoeff B 120 := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop 120 (by norm_num))
  have h80 : supportCoeff A (80 * p) =
      supportCoeff A 80 + supportCoeff B 80 := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop 80 (by norm_num))
  have h48 : supportCoeff A (48 * p) =
      supportCoeff A 48 + supportCoeff B 48 := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop 48 (by norm_num))
  have h40 : supportCoeff A (40 * p) =
      supportCoeff A 40 + supportCoeff B 40 := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop 40 (by norm_num))
  have h24 : supportCoeff A (24 * p) =
      supportCoeff A 24 + supportCoeff B 24 := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop 24 (by norm_num))
  have h16 : supportCoeff A (16 * p) =
      supportCoeff A 16 + supportCoeff B 16 := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop 16 (by norm_num))
  have h8 : supportCoeff A (8 * p) =
      supportCoeff A 8 + supportCoeff B 8 := by
    simpa only [Nat.mul_comm] using supportCoeff_mul_prime A hp (hcop 8 (by norm_num))
  have hcolumnRaw := selectedDivisors_union_three_card_identity B
    (a := 120) (b := 80) (c := 48) (by norm_num) (by norm_num) (by norm_num)
  have hcolumn :
      twentyOnePrimePullbackColumnLoad p + supportCoeff B 40 +
          supportCoeff B 24 + supportCoeff B 16 =
        supportCoeff B 120 + supportCoeff B 80 + supportCoeff B 48 +
          supportCoeff B 8 := by
    norm_num at hcolumnRaw
    simpa only [twentyOnePrimePullbackColumnLoad, A, B,
      Finset.union_assoc] using hcolumnRaw
  have htop40p := twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
    (n := 40 * p) (by positivity)
  have htop24p := twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
    (n := 24 * p) (by positivity)
  have htop8p := twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
    (n := 8 * p) (by positivity)
  have htop40 := twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
    (n := 40) (by norm_num)
  have htop24 := twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
    (n := 24) (by norm_num)
  have htop8 := twentyOneSupportCoeff_two_mul_eq_add_topTwoAdicLayer
    (n := 8) (by norm_num)
  dsimp only [twentyOneDoubledRepairPayment]
  change supportCoeff A (120 * p) + twentyOneTopTwoAdicLayerLoad (40 * p) +
          twentyOneTopTwoAdicLayerLoad (24 * p) +
          twentyOneTopTwoAdicLayerLoad 8 =
        (supportCoeff A (120 * 1) + twentyOneTopTwoAdicLayerLoad (40 * 1) +
          twentyOneTopTwoAdicLayerLoad (24 * 1)) +
          twentyOnePrimePullbackColumnLoad p +
            twentyOneTopTwoAdicLayerLoad (8 * p)
  norm_num only [Nat.mul_one] at ⊢
  norm_num only [show 2 * (40 * p) = 80 * p by omega,
    show 2 * (24 * p) = 48 * p by omega,
    show 2 * (8 * p) = 16 * p by omega,
    show 2 * 40 = 80 by norm_num, show 2 * 24 = 48 by norm_num,
    show 2 * 8 = 16 by norm_num] at htop40p htop24p htop8p htop40 htop24 htop8
  change supportCoeff A (120 * p) + twentyOneTopTwoAdicLayerLoad (40 * p) +
          twentyOneTopTwoAdicLayerLoad (24 * p) +
          twentyOneTopTwoAdicLayerLoad 8 =
        supportCoeff A 120 + twentyOneTopTwoAdicLayerLoad 40 +
          twentyOneTopTwoAdicLayerLoad 24 +
          twentyOnePrimePullbackColumnLoad p +
            twentyOneTopTwoAdicLayerLoad (8 * p)
  dsimp only [A] at h120 h80 h48 h40 h24 h16 h8 htop40p htop24p htop8p htop40 htop24 htop8 ⊢
  omega

/-- Set-level form of the same cancellation: the causal union at `240*p`
is the fixed union at `240` plus the nineteen-position pullback column. -/
theorem twentyOnePrimorialUnionLoad_primeColumn
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    twentyOnePrimorialUnionLoad (240 * p) =
      twentyOnePrimorialUnionLoad 240 +
        twentyOnePrimePullbackColumnLoad p := by
  have hpayment := twentyOneDoubledRepairPayment_primeColumn hp hp5
  have hp0 : 0 < p := hp.pos
  have hpPred : p - 1 + 1 = p := by omega
  have hlayerp := twentyOnePrimorialUnionLoad_multiple240_topTwoAdicLayer (p - 1)
  have hlayer1 := twentyOnePrimorialUnionLoad_multiple240_topTwoAdicLayer 0
  dsimp only at hlayerp hlayer1
  rw [hpPred] at hlayerp
  norm_num only [Nat.zero_add, Nat.mul_one] at hlayer1
  have hlayerp' :
      twentyOnePrimorialUnionLoad (240 * p) +
          twentyOneTopTwoAdicLayerLoad (8 * p) =
        twentyOneDoubledRepairPayment p := by
    simpa only [twentyOneDoubledRepairPayment] using hlayerp
  have hlayer1' :
      twentyOnePrimorialUnionLoad 240 +
          twentyOneTopTwoAdicLayerLoad 8 =
        twentyOneDoubledRepairPayment 1 := by
    simpa only [twentyOneDoubledRepairPayment, Nat.mul_one] using hlayer1
  omega

/-- For a prime cofactor above `5`, the old coupled boundary is equivalent to
one defect-versus-column inequality.  No denominator estimate remains: all
prime dependence on the payment side is the fixed pullback column. -/
theorem twentyOneDoubledRepairPrimeBoundary_iff_column
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    twentyOneDoubledRepairDebt p + 2 ≤ twentyOneDoubledRepairPayment p ↔
      twentyOneGreedyDefect (240 * p - 1) +
            twentyOneTopTwoAdicLayerLoad 8 + 2 ≤
        twentyOneDoubledRepairPayment 1 +
          twentyOnePrimePullbackColumnLoad p := by
  have hcolumn := twentyOneDoubledRepairPayment_primeColumn hp hp5
  dsimp only [twentyOneDoubledRepairDebt]
  omega

/-- Direct `PU240+` normal form at a prime cofactor.  This version exposes
the fixed base union rather than the payment/debt packaging. -/
theorem twentyOnePrimePrimorialRepair_iff_column
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    twentyOneGreedyDefect (240 * p - 1) + 2 ≤
        twentyOnePrimorialUnionLoad (240 * p) ↔
      twentyOneGreedyDefect (240 * p - 1) + 2 ≤
        twentyOnePrimorialUnionLoad 240 +
          twentyOnePrimePullbackColumnLoad p := by
  rw [twentyOnePrimorialUnionLoad_primeColumn hp hp5]

/-- Numerical prime-column form after kernel-certifying the base union as
seven.  This is the final infinite boundary visible in the computation. -/
theorem twentyOnePrimePrimorialRepair_iff_defect_le_column_add_five
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    twentyOneGreedyDefect (240 * p - 1) + 2 ≤
        twentyOnePrimorialUnionLoad (240 * p) ↔
      twentyOneGreedyDefect (240 * p - 1) ≤
        twentyOnePrimePullbackColumnLoad p + 5 := by
  rw [twentyOnePrimorialUnionLoad_primeColumn hp hp5,
    twentyOnePrimorialUnionLoad_240]
  omega

/-- The all-depth prime-column producer isolated by the exact normal form.
It is retained as a typed falsified boundary: the deeper certified orbit gives
a counterexample at the prime `p = 22067`.  The values `2`, `3`, and `5` are
excluded because their columns overlap the fixed modulus. -/
def TwentyOnePrimePullbackColumnBound : Prop :=
  ∀ p : ℕ, p.Prime → 5 < p →
    twentyOneGreedyDefect (240 * p - 1) ≤
      twentyOnePrimePullbackColumnLoad p + 5

/-- Open arithmetic producer: away from the isolated cofactor `16`, every
composite cofactor has a proper divisor whose coupled payment-minus-debt
balance is no larger.  The cross-multiplied form avoids integer subtraction. -/
def TwentyOneDoubledRepairFactorDescent : Prop :=
  ∀ m : ℕ, 1 < m → ¬ Nat.Prime m → m ≠ 16 →
    ∃ a : ℕ, 0 < a ∧ a < m ∧ a ∣ m ∧
      twentyOneDoubledRepairPayment a + twentyOneDoubledRepairDebt m ≤
        twentyOneDoubledRepairPayment m + twentyOneDoubledRepairDebt a

/-- Boundary producer after factor descent.  It is now known to fail at prime
cofactors; the definition remains the exact hypothesis consumed below. -/
def TwentyOneDoubledRepairPrimeBoundary : Prop :=
  twentyOneDoubledRepairDebt 1 + 2 ≤ twentyOneDoubledRepairPayment 1 ∧
    twentyOneDoubledRepairDebt 16 + 2 ≤ twentyOneDoubledRepairPayment 16 ∧
      ∀ p : ℕ, Nat.Prime p →
        twentyOneDoubledRepairDebt p + 2 ≤
          twentyOneDoubledRepairPayment p

/-- The infinite part of the prime boundary is exactly the nineteen-bit
pullback-column bound.  Only five explicit rows remain outside it. -/
theorem twentyOneDoubledRepairPrimeBoundary_of_columnBound
    (hunit : twentyOneDoubledRepairDebt 1 + 2 ≤
      twentyOneDoubledRepairPayment 1)
    (h16 : twentyOneDoubledRepairDebt 16 + 2 ≤
      twentyOneDoubledRepairPayment 16)
    (h2 : twentyOneDoubledRepairDebt 2 + 2 ≤
      twentyOneDoubledRepairPayment 2)
    (h3 : twentyOneDoubledRepairDebt 3 + 2 ≤
      twentyOneDoubledRepairPayment 3)
    (h5 : twentyOneDoubledRepairDebt 5 + 2 ≤
      twentyOneDoubledRepairPayment 5)
    (hcolumn : TwentyOnePrimePullbackColumnBound) :
    TwentyOneDoubledRepairPrimeBoundary := by
  refine ⟨hunit, h16, ?_⟩
  intro p hp
  by_cases hp5 : 5 < p
  · have hrepair :
        twentyOneGreedyDefect (240 * p - 1) + 2 ≤
          twentyOnePrimorialUnionLoad (240 * p) :=
      (twentyOnePrimePrimorialRepair_iff_defect_le_column_add_five hp hp5).2
        (hcolumn p hp hp5)
    have hlayer := twentyOnePrimorialUnionLoad_multiple240_topTwoAdicLayer (p - 1)
    have hpPred : p - 1 + 1 = p := by omega
    dsimp only at hlayer
    rw [hpPred] at hlayer
    dsimp only [twentyOneDoubledRepairDebt,
      twentyOneDoubledRepairPayment]
    omega
  · have hpLe : p ≤ 5 := by omega
    interval_cases p
    · norm_num at hp
    · norm_num at hp
    · simpa using h2
    · simpa using h3
    · norm_num at hp
    · simpa using h5

/-- Coupled factor descent plus the prime boundary proves the full doubled-row
repair.  This is the strong-induction consumer for the exact largest-prime
factor discriminator; neither premise is asserted unconditionally. -/
theorem twentyOneMultiple240PrimorialRepairSlack_of_coupledFactorDescent
    (hdescent : TwentyOneDoubledRepairFactorDescent)
    (hboundary : TwentyOneDoubledRepairPrimeBoundary) :
    TwentyOneMultiple240PrimorialRepairSlack := by
  have hrepairAt : ∀ m : ℕ, 0 < m →
      twentyOneDoubledRepairDebt m + 2 ≤
        twentyOneDoubledRepairPayment m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hmpos
        by_cases hm1 : m = 1
        · simpa only [hm1] using hboundary.1
        by_cases hm16 : m = 16
        · simpa only [hm16] using hboundary.2.1
        by_cases hprime : Nat.Prime m
        · exact hboundary.2.2 m hprime
        have hmgt : 1 < m := by omega
        rcases hdescent m hmgt hprime hm16 with
          ⟨a, hapos, halt, -, hbalance⟩
        have haRepair := ih a halt hapos
        omega
  intro k
  let m := k + 1
  have hmpos : 0 < m := by simp [m]
  have hbalance := hrepairAt m hmpos
  have hlayer :
      twentyOnePrimorialUnionLoad (240 * m) +
            twentyOneTopTwoAdicLayerLoad (8 * m) =
        supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) (120 * m) +
          twentyOneTopTwoAdicLayerLoad (40 * m) +
            twentyOneTopTwoAdicLayerLoad (24 * m) := by
    simpa only [m] using
      twentyOnePrimorialUnionLoad_multiple240_topTwoAdicLayer k
  dsimp only [twentyOneDoubledRepairDebt,
    twentyOneDoubledRepairPayment] at hbalance
  simpa only [m] using (show
    twentyOneGreedyDefect (240 * m - 1) + 2 ≤
      twentyOnePrimorialUnionLoad (240 * m) by omega)

/-- `PU120` implies the cofinal defect non-rise candidate. -/
theorem twentyOneMultiple120DefectNonrise_of_primorialRepair
    (hrepair : TwentyOneMultiple120PrimorialRepair) :
    TwentyOneMultiple120DefectNonrise := by
  intro k
  let n := 120 * (k + 1)
  have hn : 0 < n := by simp [n]
  have h30 : 30 ∣ n := by
    dsimp [n]
    omega
  have hload :
      twentyOneGreedyDefect (n - 1) + 1 ≤
        supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) n := by
    exact (hrepair k).trans
      (twentyOnePrimorialUnionLoad_le_supportCoeff hn h30)
  have hpred : n - 1 + 1 = n := by omega
  have hrec := twentyOneGreedyDefect_succ (n - 1)
  rw [hpred] at hrec
  have hbit : twentyOneFloorBit (n - 1) = 1 := by
    simpa only [n] using twentyOneFloorBit_pred_multiple120 k
  have hloadZ :
      (twentyOneGreedyDefect (n - 1) : ℤ) + 1 ≤
        (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) n : ℤ) := by
    exact_mod_cast hload
  have hnonriseZ :
      (twentyOneGreedyDefect n : ℤ) ≤
        (twentyOneGreedyDefect (n - 1) : ℤ) := by
    rw [hbit] at hrec
    omega
  exact_mod_cast hnonriseZ

/-- Any one-step non-rise of the denominator-21 defect gives a linear bound
at that rank.  This is the arithmetic shortcut missed by the earlier
record-cofiniteness formulation: no eventual record theorem is needed. -/
theorem twentyOneGreedyDefect_le_rank_of_nonrise
    {n : ℕ} (hn : 0 < n)
    (hnonrise : twentyOneGreedyDefect n ≤
      twentyOneGreedyDefect (n - 1)) :
    twentyOneGreedyDefect n ≤ n := by
  let A := greedyMersenneSupport (1 / 21 : ℝ)
  let f := supportCoeff A
  have hpred : n - 1 + 1 = n := by omega
  have hrec :
      (twentyOneGreedyDefect n : ℤ) =
        2 * (twentyOneGreedyDefect (n - 1) : ℤ) +
          twentyOneFloorBit (n - 1) - (f n : ℤ) := by
    simpa only [hpred] using twentyOneGreedyDefect_succ (n - 1)
  have hbit : 0 ≤ twentyOneFloorBit (n - 1) := by
    rw [twentyOneFloorBit_eq_two_mul_mod_div]
    positivity
  have hnonriseZ :
      (twentyOneGreedyDefect n : ℤ) ≤
        (twentyOneGreedyDefect (n - 1) : ℤ) := by
    exact_mod_cast hnonrise
  have hq_le_f : twentyOneGreedyDefect (n - 1) ≤ f n := by
    exact_mod_cast (show
      (twentyOneGreedyDefect (n - 1) : ℤ) ≤ (f n : ℤ) by omega)
  have hf_le_n : f n ≤ n := supportCoeff_le_self A n
  exact hnonrise.trans (hq_le_f.trans hf_le_n)

/-- A defect bounded by its rank gives the exact linear carry return used by
the existing cofinal endpoint. -/
theorem twentyOneGreedyCarry_le_linear_of_defect_le_rank
    {n : ℕ} (hQ : twentyOneGreedyDefect n ≤ n) :
    twentyOneGreedyCarry n ≤ ((21 * (n + 1) : ℕ) : ℤ) := by
  rw [twentyOneGreedyCarry_eq_mod_add_defect]
  have hmod : 2 ^ n % 21 < 21 := Nat.mod_lt _ (by omega)
  have hmodZ : ((2 ^ n % 21 : ℕ) : ℤ) ≤ 20 := by
    exact_mod_cast (show 2 ^ n % 21 ≤ 20 by omega)
  have hQZ : (twentyOneGreedyDefect n : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast hQ
  push_cast
  omega

/-- The multiple-of-120 non-rise candidate supplies cofinally many linear
carry returns. -/
theorem twentyOneGreedyCarry_cofinalLinearReturn_of_multiple120DefectNonrise
    (hrepair : TwentyOneMultiple120DefectNonrise) :
    TwentyOneGreedyCarryCofinalLinearReturn := by
  intro N
  let M := 120 * (N + 1)
  have hMpos : 0 < M := by simp [M]
  have hNM : N ≤ M := by
    dsimp [M]
    omega
  have hnonrise :
      twentyOneGreedyDefect M ≤ twentyOneGreedyDefect (M - 1) := by
    simpa only [M] using hrepair N
  have hQ : twentyOneGreedyDefect M ≤ M :=
    twentyOneGreedyDefect_le_rank_of_nonrise hMpos hnonrise
  exact ⟨M, hNM, twentyOneGreedyCarry_le_linear_of_defect_le_rank hQ⟩

/-- **Checked consumer.**  Proving the all-depth repair at multiples of `120`
puts `1 / 21` in the Mersenne achievement set. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_multiple120DefectNonrise
    (hrepair : TwentyOneMultiple120DefectNonrise) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  exact one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalLinearReturn
    (twentyOneGreedyCarry_cofinalLinearReturn_of_multiple120DefectNonrise
      hrepair)

/-- **Exact finite producer-to-endpoint chain.**  The all-depth seven-column
primorial repair implies membership of `1 / 21`. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_primorialRepair
    (hrepair : TwentyOneMultiple120PrimorialRepair) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  exact one_div_twenty_one_mem_mersenneAchievementSet_of_multiple120DefectNonrise
    (twentyOneMultiple120DefectNonrise_of_primorialRepair hrepair)

/-- **Doubled-row consumer.**  The one-unit-slack repair on the cofinal
modulus-`240` rows alone already proves membership of `1 / 21`. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_multiple240PrimorialRepairSlack
    (hrepair : TwentyOneMultiple240PrimorialRepairSlack) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalLinearReturn
  intro N
  let M := 240 * (N + 1)
  have hMpos : 0 < M := by simp [M]
  have hNM : N ≤ M := by
    dsimp [M]
    omega
  have h30 : 30 ∣ M := by
    dsimp [M]
    omega
  have hload :
      twentyOneGreedyDefect (M - 1) + 1 ≤
        supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) M := by
    have hrepair' :
        twentyOneGreedyDefect (M - 1) + 2 ≤
          twentyOnePrimorialUnionLoad M := by
      simpa only [M] using hrepair N
    exact (by omega : twentyOneGreedyDefect (M - 1) + 1 ≤
      twentyOneGreedyDefect (M - 1) + 2).trans
        (hrepair'.trans
          (twentyOnePrimorialUnionLoad_le_supportCoeff hMpos h30))
  have hpred : M - 1 + 1 = M := by omega
  have hrec := twentyOneGreedyDefect_succ (M - 1)
  rw [hpred] at hrec
  have hbit : twentyOneFloorBit (M - 1) = 1 := by
    have hindex : 120 * (2 * N + 1 + 1) - 1 = M - 1 := by
      dsimp [M]
      omega
    rw [← hindex]
    exact twentyOneFloorBit_pred_multiple120 (2 * N + 1)
  have hloadZ :
      (twentyOneGreedyDefect (M - 1) : ℤ) + 1 ≤
        (supportCoeff (greedyMersenneSupport (1 / 21 : ℝ)) M : ℤ) := by
    exact_mod_cast hload
  have hnonriseZ :
      (twentyOneGreedyDefect M : ℤ) ≤
        (twentyOneGreedyDefect (M - 1) : ℤ) := by
    rw [hbit] at hrec
    omega
  have hnonrise :
      twentyOneGreedyDefect M ≤ twentyOneGreedyDefect (M - 1) := by
    exact_mod_cast hnonriseZ
  have hQ : twentyOneGreedyDefect M ≤ M :=
    twentyOneGreedyDefect_le_rank_of_nonrise hMpos hnonrise
  exact ⟨M, hNM, twentyOneGreedyCarry_le_linear_of_defect_le_rank hQ⟩

/-- **Prime-boundary consumer.**  The coupled factor-descent law reduces the
all-depth counterexample producer to the unit row, cofactor `16`, and prime
cofactors. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_coupledFactorDescent
    (hdescent : TwentyOneDoubledRepairFactorDescent)
    (hboundary : TwentyOneDoubledRepairPrimeBoundary) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  exact
    one_div_twenty_one_mem_mersenneAchievementSet_of_multiple240PrimorialRepairSlack
      (twentyOneMultiple240PrimorialRepairSlack_of_coupledFactorDescent
        hdescent hboundary)

/-- **Nineteen-column conditional endpoint.**  Coupled factor descent, five
finite base rows, and the (now falsified) all-prime pullback-column bound would
prove the rational counterexample target. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_primeColumnBound
    (hdescent : TwentyOneDoubledRepairFactorDescent)
    (hunit : twentyOneDoubledRepairDebt 1 + 2 ≤
      twentyOneDoubledRepairPayment 1)
    (h16 : twentyOneDoubledRepairDebt 16 + 2 ≤
      twentyOneDoubledRepairPayment 16)
    (h2 : twentyOneDoubledRepairDebt 2 + 2 ≤
      twentyOneDoubledRepairPayment 2)
    (h3 : twentyOneDoubledRepairDebt 3 + 2 ≤
      twentyOneDoubledRepairPayment 3)
    (h5 : twentyOneDoubledRepairDebt 5 + 2 ≤
      twentyOneDoubledRepairPayment 5)
    (hcolumn : TwentyOnePrimePullbackColumnBound) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  exact one_div_twenty_one_mem_mersenneAchievementSet_of_coupledFactorDescent
    hdescent
    (twentyOneDoubledRepairPrimeBoundary_of_columnBound
      hunit h16 h2 h3 h5 hcolumn)

#print axioms twentyOneGreedyDefect_le_rank_of_nonrise
#print axioms twentyOneGreedyCarry_le_linear_of_defect_le_rank
#print axioms
  twentyOneGreedyCarry_cofinalLinearReturn_of_multiple120DefectNonrise
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_multiple120DefectNonrise
#print axioms twentyOnePrimorialUnionLoad_sevenColumn
#print axioms twentyOneMultiple120DefectNonrise_of_primorialRepair
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_primorialRepair
#print axioms twentyOnePrimorialUnionLoad_multiple240_topTwoAdicLayer
#print axioms twentyOnePrimorialUnionLoad_240
#print axioms twentyOneDoubledRepairPayment_primeColumn
#print axioms twentyOnePrimorialUnionLoad_primeColumn
#print axioms twentyOneDoubledRepairPrimeBoundary_iff_column
#print axioms twentyOnePrimePrimorialRepair_iff_defect_le_column_add_five
#print axioms twentyOneDoubledRepairPrimeBoundary_of_columnBound
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_multiple240PrimorialRepairSlack
#print axioms
  twentyOneMultiple240PrimorialRepairSlack_of_coupledFactorDescent
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_coupledFactorDescent
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_primeColumnBound

end ErdosProblems.Erdos257
