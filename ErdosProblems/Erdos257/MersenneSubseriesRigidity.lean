import Erdos249257.GreedyAchievementSet

/-!
# Erdős #257: hereditary Mersenne subseries rigidity

Let `J` be the set of allowed Mersenne coordinates.  This module proves that
the corresponding subseries still has unique binary coding and a compact,
nowhere-dense achievement set.  If `J` is infinite, that set is perfect.  Its
Lebesgue measure is positive exactly when only finitely many coordinates are
forbidden; omitting a finite set `F` gives measure `2^(-|F|)`, while omitting
infinitely many coordinates gives measure zero.

The arithmetic bridge identifies this achievement set with convergent
support-restricted Mersenne subseries.  These hereditary geometric results do
not settle the universal irrationality problem.
-/

namespace ErdosProblems.Erdos257

open scoped ENNReal

open Set
open MeasureTheory
open Erdos249257

/-- Mersenne tails restricted to an arbitrary set of future offsets. -/
noncomputable def selectedMersenneTail (J : Set ℕ) (n : ℕ) : ℝ :=
  ∑' k : ℕ,
    J.indicator (fun k => mersenneWeight (n + k + 1)) k

theorem summable_selectedMersenneTail (J : Set ℕ) (n : ℕ) :
    Summable (J.indicator (fun k => mersenneWeight (n + k + 1))) :=
  (summable_mersenneTail n).indicator J

/-- Strict superincreasingness is hereditary under deleting any collection of
future Mersenne weights. -/
theorem selectedMersenneTail_lt_weight
    (J : Set ℕ) {n : ℕ} (hn : 0 < n) :
    selectedMersenneTail J n < mersenneWeight n := by
  have hle : selectedMersenneTail J n ≤ mersenneTail n := by
    unfold selectedMersenneTail mersenneTail
    exact (summable_selectedMersenneTail J n).tsum_le_tsum
      (fun k => by
        by_cases hk : k ∈ J
        · rw [Set.indicator_of_mem hk]
        · rw [Set.indicator_of_notMem hk]
          exact (mersenneWeight_pos (by omega : 0 < n + k + 1)).le)
      (summable_mersenneTail n)
  exact hle.trans_lt (mersenneTail_lt_weight hn)

/-- Binary digit strings supported on `J`. -/
def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}

/-- The ordinary Mersenne digit map restricted to a chosen support. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1

/-- Every Mersenne subseries retains unique binary coding. -/
theorem supportedMersenneDigitValue_injective (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) := by
  intro b c h
  apply Subtype.ext
  exact positiveMersenneDigitValue_injective h

/-! ## Arbitrary-support achievement sets -/

/-- Supported binary strings as a closed subset of the full product space. -/
def supportedMersenneDigitSet (J : Set ℕ) : Set (ℕ → Fin 2) :=
  {b | ∀ k, k ∉ J → b k = 0}

theorem isClosed_supportedMersenneDigitSet (J : Set ℕ) :
    IsClosed (supportedMersenneDigitSet J) := by
  rw [show supportedMersenneDigitSet J =
      ⋂ k ∈ Jᶜ, {b : ℕ → Fin 2 | b k = 0} by
    ext b
    simp [supportedMersenneDigitSet]]
  exact isClosed_biInter fun k _ =>
    isClosed_eq (continuous_apply k) continuous_const

/-- The achievement set obtained by allowing digits only on `J`. -/
def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)

theorem supportedMersenneAchievementSet_eq_image (J : Set ℕ) :
    supportedMersenneAchievementSet J =
      positiveMersenneDigitValue '' supportedMersenneDigitSet J := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.1, b.2, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

/-- Arithmetic interpretation of the restricted achievement set.  Allowing
the digit coordinates in `J` is exactly the same as allowing support exponents
in the shifted set `Nat.succ '' J`; the analytically invisible exponent zero
is excluded explicitly. -/
theorem mem_supportedMersenneAchievementSet_iff_exists_support_series
    (J : Set ℕ) (x : ℝ) :
    x ∈ supportedMersenneAchievementSet J ↔
      ∃ A : Set ℕ,
        0 ∉ A ∧
        A ⊆ Nat.succ '' J ∧
        erdosSupportSeries 2 A = x := by
  classical
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨mersenneDigitSupport b.1,
      zero_not_mem_mersenneDigitSupport b.1, ?_, ?_⟩
    · intro n hn
      rcases hn with ⟨k, rfl, hbk⟩
      have hkJ : k ∈ J := by
        by_contra hkJ
        have hb0 := b.2 k hkJ
        simp [hbk] at hb0
      exact ⟨k, hkJ, rfl⟩
    · calc
        erdosSupportSeries 2 (mersenneDigitSupport b.1) =
            positiveMersenneSupportValue (mersenneDigitSupport b.1) :=
          (positiveMersenneSupportValue_eq_erdosSupportSeries _).symm
        _ = positiveMersenneDigitValue b.1 :=
          (positiveMersenneDigitValue_eq_supportValue b.1).symm
        _ = supportedMersenneDigitValue J b := rfl
  · rintro ⟨A, hA0, hAJ, hvalue⟩
    let b : ℕ → Fin 2 := fun k => if k + 1 ∈ A then 1 else 0
    have hb : ∀ k, k ∉ J → b k = 0 := by
      intro k hkJ
      have hkA : k + 1 ∉ A := by
        intro hkA
        rcases hAJ hkA with ⟨j, hjJ, hjk⟩
        have hjkeq : j = k := by omega
        exact hkJ (hjkeq ▸ hjJ)
      simp [b, hkA]
    have hsupport : mersenneDigitSupport b = A := by
      ext n
      cases n with
      | zero => simp [hA0]
      | succ k => simp [b]
    refine ⟨⟨b, hb⟩, ?_⟩
    calc
      supportedMersenneDigitValue J ⟨b, hb⟩ =
          positiveMersenneDigitValue b := rfl
      _ = positiveMersenneSupportValue (mersenneDigitSupport b) :=
        positiveMersenneDigitValue_eq_supportValue b
      _ = positiveMersenneSupportValue A := by rw [hsupport]
      _ = erdosSupportSeries 2 A :=
        positiveMersenneSupportValue_eq_erdosSupportSeries A
      _ = x := hvalue

/-- Every support-restricted Mersenne achievement set is compact. -/
theorem isCompact_supportedMersenneAchievementSet (J : Set ℕ) :
    IsCompact (supportedMersenneAchievementSet J) := by
  rw [supportedMersenneAchievementSet_eq_image]
  exact (isClosed_supportedMersenneDigitSet J).isCompact.image
    continuous_positiveMersenneDigitValue

theorem isClosed_supportedMersenneAchievementSet (J : Set ℕ) :
    IsClosed (supportedMersenneAchievementSet J) :=
  (isCompact_supportedMersenneAchievementSet J).isClosed

/-- Deleting coordinates really produces a subset of the full Mersenne
achievement set; unique coding prevents any hidden re-entry through another
digit string. -/
theorem supportedMersenneAchievementSet_subset (J : Set ℕ) :
    supportedMersenneAchievementSet J ⊆ mersenneAchievementSet := by
  rw [← range_positiveMersenneDigitValue_eq]
  rintro _ ⟨b, rfl⟩
  exact ⟨b.1, rfl⟩

/-- Nowhere density is hereditary for every selected support, finite or
infinite.  In particular no support-restricted Mersenne achievement set can
contain an interval. -/
theorem isNowhereDense_supportedMersenneAchievementSet (J : Set ℕ) :
    IsNowhereDense (supportedMersenneAchievementSet J) :=
  isNowhereDense_mersenneAchievementSet.mono
    (supportedMersenneAchievementSet_subset J)

/-- If the selected support is infinite, its closed digit subspace has no
isolated point: every basic product neighbourhood leaves some selected
coordinate free to flip. -/
theorem preperfect_supportedMersenneDigitSet
    {J : Set ℕ} (hJ : J.Infinite) :
    Preperfect (supportedMersenneDigitSet J) := by
  rw [preperfect_iff_nhds]
  intro b hb U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  rcases hU with ⟨I, t, ht, hsub⟩
  obtain ⟨n, hnJ, hnI⟩ := hJ.exists_notMem_finset I
  let b' := Function.update b n (mersenneBitFlip (b n))
  refine ⟨b', ⟨?_, ?_⟩, ?_⟩
  · apply hsub
    intro i hi
    have hin : i ≠ n := by
      intro h
      apply hnI
      simpa [h] using hi
    change Function.update b n (mersenneBitFlip (b n)) i ∈ t i
    simpa [Function.update, hin] using mem_of_mem_nhds (ht i)
  · intro k hkJ
    have hkn : k ≠ n := by
      intro h
      apply hkJ
      simpa [h] using hnJ
    change Function.update b n (mersenneBitFlip (b n)) k = 0
    simpa [Function.update, hkn] using hb k hkJ
  · intro h
    have hnEq := congrFun h n
    change Function.update b n (mersenneBitFlip (b n)) n = b n at hnEq
    exact mersenneBitFlip_ne (b n) (by simpa [Function.update] using hnEq)

theorem preperfect_supportedMersenneAchievementSet
    {J : Set ℕ} (hJ : J.Infinite) :
    Preperfect (supportedMersenneAchievementSet J) := by
  rw [supportedMersenneAchievementSet_eq_image, preperfect_iff_nhds]
  rintro x ⟨b, hb, rfl⟩ U hU
  have hpre :=
    (preperfect_iff_nhds.mp (preperfect_supportedMersenneDigitSet hJ))
      b hb (positiveMersenneDigitValue ⁻¹' U)
      (continuous_positiveMersenneDigitValue.continuousAt hU)
  rcases hpre with ⟨c, hc, hcb⟩
  refine ⟨positiveMersenneDigitValue c,
    ⟨hc.1, ⟨c, hc.2, rfl⟩⟩, ?_⟩
  intro h
  exact hcb (positiveMersenneDigitValue_injective h)

/-- Every infinite selected support produces a compact perfect nowhere-dense
set with unique coding. -/
theorem perfect_supportedMersenneAchievementSet
    {J : Set ℕ} (hJ : J.Infinite) :
    Perfect (supportedMersenneAchievementSet J) :=
  ⟨isClosed_supportedMersenneAchievementSet J,
    preperfect_supportedMersenneAchievementSet hJ⟩

/-! ## One-coordinate splitting -/

theorem summable_mersenneDigitTerm (b : ℕ → Fin 2) :
    Summable (fun k => mersenneDigitTerm k b) :=
  summable_mersenneWeight.of_norm_bounded fun k =>
    norm_mersenneDigitTerm_le k b

/-- Updating one binary coordinate changes the coded value by exactly the
corresponding signed Mersenne weight. -/
theorem positiveMersenneDigitValue_update
    (b : ℕ → Fin 2) (k : ℕ) (a : Fin 2) :
    positiveMersenneDigitValue (Function.update b k a) =
      ((((a : ℕ) : ℝ) - ((b k : ℕ) : ℝ)) * mersenneWeight (k + 1)) +
        positiveMersenneDigitValue b := by
  have hfun :
      (fun j => mersenneDigitTerm j (Function.update b k a)) =
        Function.update (fun j => mersenneDigitTerm j b) k
          (((a : ℕ) : ℝ) * mersenneWeight (k + 1)) := by
    funext j
    by_cases hj : j = k
    · subst j
      simp [mersenneDigitTerm, Function.update]
    · simp [mersenneDigitTerm, Function.update, hj]
  rw [positiveMersenneDigitValue, hfun]
  simpa [mersenneDigitTerm, positiveMersenneDigitValue, sub_mul] using
    ((summable_mersenneDigitTerm b).hasSum.update k
      (((a : ℕ) : ℝ) * mersenneWeight (k + 1))).tsum_eq

/-- Adding one previously forbidden coordinate splits the achievement set
into its zero face and a translate of that face. -/
theorem supportedMersenneAchievementSet_insert
    {J : Set ℕ} {k : ℕ} (hk : k ∉ J) :
    supportedMersenneAchievementSet (insert k J) =
      supportedMersenneAchievementSet J ∪
        (fun x : ℝ => mersenneWeight (k + 1) + x) ''
          supportedMersenneAchievementSet J := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    by_cases hbk : b.1 k = 0
    · left
      refine ⟨⟨b.1, ?_⟩, rfl⟩
      intro i hiJ
      by_cases hik : i = k
      · simpa [hik] using hbk
      · exact b.2 i (by simp [hik, hiJ])
    · have hbk1 : b.1 k = 1 := Fin.eq_one_of_ne_zero (b.1 k) hbk
      let c : ℕ → Fin 2 := Function.update b.1 k 0
      have hcJ : ∀ i, i ∉ J → c i = 0 := by
        intro i hiJ
        by_cases hik : i = k
        · simp [c, hik]
        · simpa [c, Function.update, hik] using b.2 i (by simp [hik, hiJ])
      have hck : c k = 0 := by simp [c]
      have hcb : Function.update c k 1 = b.1 := by
        funext i
        by_cases hik : i = k
        · subst i
          simp [c, Function.update, hbk1]
        · simp [c, Function.update, hik]
      have hvalue :
          positiveMersenneDigitValue b.1 =
            mersenneWeight (k + 1) + positiveMersenneDigitValue c := by
        have h := positiveMersenneDigitValue_update c k 1
        rw [hcb] at h
        simpa [hck] using h
      right
      refine ⟨positiveMersenneDigitValue c, ⟨⟨c, hcJ⟩, rfl⟩, ?_⟩
      exact hvalue.symm
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨b, rfl⟩
      refine ⟨⟨b.1, ?_⟩, rfl⟩
      intro i hi
      exact b.2 i (fun hiJ => hi (Set.mem_insert_of_mem k hiJ))
    · rcases hx with ⟨_, ⟨b, rfl⟩, rfl⟩
      have hbk : b.1 k = 0 := b.2 k hk
      let c : ℕ → Fin 2 := Function.update b.1 k 1
      have hc : ∀ i, i ∉ insert k J → c i = 0 := by
        intro i hi
        have hik : i ≠ k := fun h => hi (by simpa [h])
        have hiJ : i ∉ J := fun h => hi (Set.mem_insert_of_mem k h)
        simpa [c, Function.update, hik] using b.2 i hiJ
      refine ⟨⟨c, hc⟩, ?_⟩
      have h := positiveMersenneDigitValue_update b.1 k 1
      simpa [c, hbk] using h

/-- The two faces in the one-coordinate split are disjoint.  This is exactly
where unique coding is spent. -/
theorem disjoint_supportedMersenneAchievementSet_translate
    {J : Set ℕ} {k : ℕ} (hk : k ∉ J) :
    Disjoint (supportedMersenneAchievementSet J)
      ((fun x : ℝ => mersenneWeight (k + 1) + x) ''
        supportedMersenneAchievementSet J) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with ⟨b, rfl⟩
  rcases hy with ⟨_, ⟨c, rfl⟩, hvalue⟩
  have hbk : b.1 k = 0 := b.2 k hk
  have hck : c.1 k = 0 := c.2 k hk
  have hupdate :
      positiveMersenneDigitValue (Function.update c.1 k 1) =
        mersenneWeight (k + 1) + positiveMersenneDigitValue c.1 := by
    simpa [hck] using positiveMersenneDigitValue_update c.1 k 1
  have heq :
      positiveMersenneDigitValue (Function.update c.1 k 1) =
        positiveMersenneDigitValue b.1 := hupdate.trans hvalue
  have hdigits := positiveMersenneDigitValue_injective heq
  have hkEq := congrFun hdigits k
  simp [Function.update, hbk] at hkEq

/-- Allowing one new coordinate doubles Lebesgue measure: the two faces are
disjoint translates of the same compact measurable set. -/
theorem volume_supportedMersenneAchievementSet_insert
    {J : Set ℕ} {k : ℕ} (hk : k ∉ J) :
    volume (supportedMersenneAchievementSet (insert k J)) =
      2 * volume (supportedMersenneAchievementSet J) := by
  rw [supportedMersenneAchievementSet_insert hk]
  have hmeas : MeasurableSet
      ((fun x : ℝ => mersenneWeight (k + 1) + x) ''
        supportedMersenneAchievementSet J) :=
    ((isCompact_supportedMersenneAchievementSet J).image
      (continuous_const.add continuous_id)).isClosed.measurableSet
  rw [measure_union (disjoint_supportedMersenneAchievementSet_translate hk) hmeas]
  rw [Set.image_add_left, measure_preimage_add]
  ring

theorem supportedMersenneAchievementSet_univ :
    supportedMersenneAchievementSet Set.univ = mersenneAchievementSet := by
  rw [← range_positiveMersenneDigitValue_eq]
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.1, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, by simp⟩, rfl⟩

/-- Finite-coordinate face volume in a division-free form.  Deleting the
coordinates in `F` and then multiplying by `2^|F|` recovers the full
measure-one Mersenne achievement set. -/
theorem volume_supportedMersenneAchievementSet_finset_compl_scaled
    (F : Finset ℕ) :
    (2 : ℝ≥0∞) ^ F.card *
        volume (supportedMersenneAchievementSet ((↑F : Set ℕ)ᶜ)) = 1 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp [supportedMersenneAchievementSet_univ,
        volume_mersenneAchievementSet]
  | @insert k F hk ih =>
      have hkSmall : k ∉ ((↑(insert k F) : Set ℕ)ᶜ) := by simp
      have hset :
          insert k ((↑(insert k F) : Set ℕ)ᶜ) = (↑F : Set ℕ)ᶜ := by
        ext i
        by_cases hik : i = k
        · subst i
          simp [hk]
        · simp [hik]
      have hvolume :=
        volume_supportedMersenneAchievementSet_insert hkSmall
      rw [hset] at hvolume
      rw [Finset.card_insert_of_notMem hk, pow_succ]
      calc
        ((2 : ℝ≥0∞) ^ F.card * 2) *
              volume (supportedMersenneAchievementSet
                ((↑(insert k F) : Set ℕ)ᶜ)) =
            (2 : ℝ≥0∞) ^ F.card *
              (2 * volume (supportedMersenneAchievementSet
                ((↑(insert k F) : Set ℕ)ᶜ))) := by ring
        _ = (2 : ℝ≥0∞) ^ F.card *
              volume (supportedMersenneAchievementSet ((↑F : Set ℕ)ᶜ)) := by
            rw [← hvolume]
        _ = 1 := ih

/-- Exact finite-codimension volume.  Forbidding exactly the coordinates in
`F` leaves a face of Lebesgue measure `2^(-|F|)`. -/
theorem volume_supportedMersenneAchievementSet_finset_compl
    (F : Finset ℕ) :
    volume (supportedMersenneAchievementSet ((↑F : Set ℕ)ᶜ)) =
      ((2 : ℝ≥0∞) ^ F.card)⁻¹ := by
  apply ENNReal.eq_inv_of_mul_eq_one_left
  simpa [mul_comm] using
    volume_supportedMersenneAchievementSet_finset_compl_scaled F

/-- Enlarging the set of allowed coordinates enlarges its achievement set. -/
theorem supportedMersenneAchievementSet_mono
    {J K : Set ℕ} (hJK : J ⊆ K) :
    supportedMersenneAchievementSet J ⊆
      supportedMersenneAchievementSet K := by
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨b.1, fun i hiK => b.2 i (fun hiJ => hiK (hJK hiJ))⟩, rfl⟩

/-- If infinitely many binary coordinates are forbidden, the supported
Mersenne achievement set has Lebesgue measure zero.  The proof traps it below
finite-codimension faces of arbitrarily small dyadic measure. -/
theorem volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite
    {J : Set ℕ} (hJ : Jᶜ.Infinite) :
    volume (supportedMersenneAchievementSet J) = 0 := by
  have hbound : ∀ n : ℕ,
      volume (supportedMersenneAchievementSet J) ≤
        ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    obtain ⟨F, hFsub, hFcard⟩ := hJ.exists_subset_card_eq n
    have hJsub : J ⊆ (↑F : Set ℕ)ᶜ := by
      intro i hiJ hiF
      exact (hFsub hiF) hiJ
    calc
      volume (supportedMersenneAchievementSet J) ≤
          volume (supportedMersenneAchievementSet ((↑F : Set ℕ)ᶜ)) :=
        measure_mono (supportedMersenneAchievementSet_mono hJsub)
      _ = ((2 : ℝ≥0∞) ^ F.card)⁻¹ :=
        volume_supportedMersenneAchievementSet_finset_compl F
      _ = ((2 : ℝ≥0∞)⁻¹) ^ n := by
        simpa [hFcard] using
          (ENNReal.inv_pow (a := (2 : ℝ≥0∞)) (n := F.card))
  apply le_antisymm ?_ bot_le
  exact ge_of_tendsto'
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1)) hbound

/-- Complete Lebesgue-measure classification of supported Mersenne
achievement sets.  Either only the finite set `F` of coordinates is omitted,
in which case the volume is exactly `2^(-|F|)`, or infinitely many
coordinates are omitted and the volume is zero. -/
theorem volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧
        volume (supportedMersenneAchievementSet J) = 0) := by
  classical
  by_cases hfinite : Jᶜ.Finite
  · left
    let F := hfinite.toFinset
    have hF : (↑F : Set ℕ)ᶜ = J := by
      change (↑hfinite.toFinset : Set ℕ)ᶜ = J
      rw [hfinite.coe_toFinset, compl_compl]
    refine ⟨F, hF.symm, ?_⟩
    have hvolume := volume_supportedMersenneAchievementSet_finset_compl F
    rw [hF] at hvolume
    exact hvolume
  · right
    have hinfinite : Jᶜ.Infinite := hfinite
    exact ⟨hinfinite,
      volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite
        hinfinite⟩

/-- A supported Mersenne achievement set has positive Lebesgue measure if and
only if the set of forbidden coordinates is finite. -/
theorem volume_supportedMersenneAchievementSet_pos_iff_compl_finite
    (J : Set ℕ) :
    0 < volume (supportedMersenneAchievementSet J) ↔ Jᶜ.Finite := by
  classical
  constructor
  · intro hvolume
    by_contra hfinite
    have hinfinite : Jᶜ.Infinite := hfinite
    rw [volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite
      hinfinite] at hvolume
    exact (lt_irrefl 0) hvolume
  · intro hfinite
    let F := hfinite.toFinset
    have hF : (↑F : Set ℕ)ᶜ = J := by
      change (↑hfinite.toFinset : Set ℕ)ᶜ = J
      rw [hfinite.coe_toFinset, compl_compl]
    rw [← hF, volume_supportedMersenneAchievementSet_finset_compl]
    exact ENNReal.inv_pos.mpr (by simp)

end ErdosProblems.Erdos257
