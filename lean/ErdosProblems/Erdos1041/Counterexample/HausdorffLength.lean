import ErdosProblems.Erdos1041.Counterexample.Assembly

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026. -/

/-!
# Erdős #1041 with length as one-dimensional Hausdorff measure

Formal Conjectures states Erdős #1041 with the length of a path defined as the
one-dimensional Hausdorff measure `μH[1]` of its image. `erdos1041_counterexample`
bounds the total variation of a parametrisation instead. This module proves the
Hausdorff form for the same polynomial `f`, and in a stronger shape: every
preconnected subset of the strict lemniscate `Ω(f)` that contains two distinct
roots has one-dimensional Hausdorff measure greater than two
(`erdos1041_counterexample_hausdorff`). The image of any path joining two roots
is such a set.

The argument reuses the bottleneck geometry of `Bottleneck.lean` and adds no
arc-extraction, rectifiability or length-of-arc lemma. Removing the slit
preimage from the component of `Ω(f)` through the critical point leaves an open
set in which no preconnected subset contains both roots, because the polynomial
restricted there is a covering of a simply connected base. So a preconnected
set `K` through both roots must, for every radius between the slit preimage and
a root, meet the circle of that radius about the critical point inside the
connected component of that root (`bottleneck_sheet_crossing`). The two
components are disjoint open sets, the distance to the critical point is
1-Lipschitz, and on the real line `μH[1]` is Lebesgue measure, so `μH[1] K` is at
least the sum of the two radial lengths (`s3_bottleneck_hausdorff`). That is the
same bound `s3_bottleneck_length` gives for total variation, so the numerical
margin of `Assembly.lean` applies unchanged.

`erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false` state the
Formal Conjectures parent `Erdos1041.erdos_1041` in its own vocabulary, with
`fcLength` its `length`, and refute it.

The mathematics of the counterexample is ani's. The polynomial is the single
member `s = 10⁻⁶` of ani's family fixed in `Defs.lean`.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Polynomial Metric

namespace Erdos1041.Counterexample

/-! ## The slit domain separates the two roots -/

/-- A root in the distinguished component lies in the slit domain: its value
`0` is not on the slit of a nonzero critical value. -/
theorem bottleneck_root_mem_slitDomain (p : Polynomial ℂ) (cc b : ℂ)
    (hv : p.eval cc ≠ 0) (hb : b ∈ connectedComponentIn (Omega p) cc)
    (hr : p.IsRoot b) :
    b ∈ bottleneckSlitDomain p cc := by
  refine ⟨hb, ?_⟩
  rw [show p.eval b = 0 from hr]
  exact zero_not_mem_bottleneckSlit (p.eval cc) hv

/-- No preconnected subset of the slit domain contains two distinct roots:
the polynomial is a covering of the simply connected slit disc there, so it is
injective along any preconnected set, and both roots have value `0`. -/
theorem bottleneck_preconnected_not_both_roots (p : Polynomial ℂ) (cc : ℂ)
    (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂) (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (S : Set ℂ) (hS : IsPreconnected S) (hSD : S ⊆ bottleneckSlitDomain p cc)
    (hb₁ : b₁ ∈ S) (hb₂ : b₂ ∈ S) : False := by
  letI : SimplyConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_simplyConnected (p.eval cc) hv
  letI : LocPathConnectedSpace (bottleneckSlitBase (p.eval cc)) :=
    bottleneckSlitBase_locPathConnected (p.eval cc) hv
  letI : PreconnectedSpace S := Subtype.preconnectedSpace hS
  let g : S → bottleneckSlitDomain p cc := fun x => ⟨x.1, hSD x.2⟩
  have hg : Continuous g := continuous_subtype_val.subtype_mk _
  have hbase : bottleneckSlitProjection p cc (g ⟨b₁, hb₁⟩) =
      bottleneckSlitProjection p cc (g ⟨b₂, hb₂⟩) := by
    apply Subtype.ext
    change p.eval b₁ = p.eval b₂
    exact (show p.eval b₁ = 0 from hr₁).trans (show p.eval b₂ = 0 from hr₂).symm
  have heq := bottleneck_covering_fibre_eq_on_preconnected
    (bottleneckSlitProjection p cc) hcover Set.univ isPreconnected_univ
    g hg.continuousOn ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ (Set.mem_univ _) (Set.mem_univ _) hbase
  exact hne (congrArg Subtype.val heq)

/-! ## Crossing every circle inside each sheet -/

/-- A preconnected set through both roots meets, for every radius `r` from the
slit radius `r₀` up to `‖b₁ - cc‖`, the circle of radius `r` about `cc` inside
the connected component of the slit domain that contains `b₁`. -/
theorem bottleneck_sheet_crossing (p : Polynomial ℂ) (cc : ℂ) (hv : p.eval cc ≠ 0)
    (hcover : IsCoveringMap (bottleneckSlitProjection p cc))
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂) (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (r₀ : ℝ)
    (hnear : ∀ z ∈ connectedComponentIn (Omega p) cc,
      p.eval z ∈ bottleneckSlit (p.eval cc) → ‖z - cc‖ < r₀)
    (K : Set ℂ) (hK : IsPreconnected K)
    (hKsub : K ⊆ connectedComponentIn (Omega p) cc)
    (hK₁ : b₁ ∈ K) (hK₂ : b₂ ∈ K)
    (r : ℝ) (hr : r ∈ Set.Ico r₀ ‖b₁ - cc‖) :
    ∃ z ∈ K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁, ‖z - cc‖ = r := by
  have hDopen : IsOpen (bottleneckSlitDomain p cc) := bottleneckSlitDomain_isOpen p cc hv
  have hD₁open : IsOpen (connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
    hDopen.connectedComponentIn
  have hD₁pre : IsPreconnected (connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
    isPreconnected_connectedComponentIn
  have hD₁D : connectedComponentIn (bottleneckSlitDomain p cc) b₁ ⊆
      bottleneckSlitDomain p cc :=
    connectedComponentIn_subset _ _
  have hb₁D : b₁ ∈ bottleneckSlitDomain p cc :=
    bottleneck_root_mem_slitDomain p cc b₁ hv hb₁ hr₁
  have hb₁D₁ : b₁ ∈ connectedComponentIn (bottleneckSlitDomain p cc) b₁ :=
    mem_connectedComponentIn hb₁D
  have hnormcont : Continuous fun w : ℂ => ‖w - cc‖ := by fun_prop
  have hclosedOuter : IsClosed {w : ℂ | r ≤ ‖w - cc‖} :=
    isClosed_le continuous_const hnormcont
  -- A point of `K` in the closure of the outer part of the sheet lies in the sheet.
  have hclosure : ∀ z ∈ K,
      z ∈ closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
        {w : ℂ | r ≤ ‖w - cc‖}) →
      z ∈ connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∧ r ≤ ‖z - cc‖ := by
    intro z hzK hzcl
    have hzr : r ≤ ‖z - cc‖ :=
      (closure_minimal Set.inter_subset_right hclosedOuter) hzcl
    have hzD : z ∈ bottleneckSlitDomain p cc := by
      refine ⟨hKsub hzK, fun hslit => ?_⟩
      have hlt := hnear z (hKsub hzK) hslit
      linarith [hr.1]
    have hzcl₁ : z ∈ closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
      closure_mono Set.inter_subset_left hzcl
    have hpre : IsPreconnected
        (insert z (connectedComponentIn (bottleneckSlitDomain p cc) b₁)) :=
      hD₁pre.subset_closure (Set.subset_insert _ _)
        (Set.insert_subset hzcl₁ subset_closure)
    have hsub : insert z (connectedComponentIn (bottleneckSlitDomain p cc) b₁) ⊆
        bottleneckSlitDomain p cc :=
      Set.insert_subset hzD hD₁D
    exact ⟨hpre.subset_connectedComponentIn (Set.mem_insert_of_mem z hb₁D₁) hsub
      (Set.mem_insert z _), hzr⟩
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hb₂not : b₂ ∉ closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r ≤ ‖w - cc‖}) := by
    intro hcl
    exact bottleneck_preconnected_not_both_roots p cc hv hcover b₁ b₂ hne hr₁ hr₂
      _ hD₁pre hD₁D hb₁D₁ (hclosure b₂ hK₂ hcl).1
  have hU : IsOpen (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r < ‖w - cc‖}) :=
    hD₁open.inter (isOpen_lt continuous_const hnormcont)
  have hV : IsOpen (closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r ≤ ‖w - cc‖}))ᶜ :=
    isClosed_closure.isOpen_compl
  have hcov : K ⊆ (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
        {w : ℂ | r < ‖w - cc‖}) ∪
      (closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
        {w : ℂ | r ≤ ‖w - cc‖}))ᶜ := by
    intro z hzK
    by_cases hzcl : z ∈ closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
        {w : ℂ | r ≤ ‖w - cc‖})
    · left
      obtain ⟨hz₁, hzr⟩ := hclosure z hzK hzcl
      exact ⟨hz₁, lt_of_le_of_ne hzr (fun h => hno z ⟨hzK, hz₁⟩ h.symm)⟩
    · exact Or.inr hzcl
  have hne₁ : (K ∩ (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r < ‖w - cc‖})).Nonempty :=
    ⟨b₁, hK₁, hb₁D₁, hr.2⟩
  have hne₂ : (K ∩ (closure (connectedComponentIn (bottleneckSlitDomain p cc) b₁ ∩
      {w : ℂ | r ≤ ‖w - cc‖}))ᶜ).Nonempty :=
    ⟨b₂, hK₂, hb₂not⟩
  obtain ⟨z, -, hzU, hzV⟩ := hK _ _ hU hV hcov hne₁ hne₂
  exact hzV (subset_closure ⟨hzU.1, (show r < ‖z - cc‖ from hzU.2).le⟩)

/-! ## From radial crossings to Hausdorff measure -/

/-- The distance to a point is 1-Lipschitz, and `μH[1]` on `ℝ` is Lebesgue
measure, so the radial image of a set is no longer than the set. -/
theorem volume_dist_image_le_hausdorff (cc : ℂ) (S : Set ℂ) :
    volume ((fun z : ℂ => dist z cc) '' S) ≤ μH[1] S := by
  have h := (LipschitzWith.dist_left cc).hausdorffMeasure_image_le
    (zero_le_one : (0 : ℝ) ≤ 1) S
  rw [hausdorffMeasure_real] at h
  simpa using h

/-- The Hausdorff-measure form of Corollary 2.4: under the disk criterion at
the critical point `cc`, every preconnected set inside the component through
both zeros has `μH[1]` at least `‖b₁ - cc‖ + ‖b₂ - cc‖ - (8/3)√(δ/‖aHat‖)`, the
same bound `s3_bottleneck_length` gives for the total variation of a path. -/
theorem s3_bottleneck_hausdorff
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (K : Set ℂ) (hK : IsPreconnected K)
    (hKsub : K ⊆ connectedComponentIn (Omega p) cc)
    (hK₁ : b₁ ∈ K) (hK₂ : b₂ ∈ K) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      ≤ μH[1] K := by
  have hdeg := bottleneck_natDegree_pos p cc b₁ hv hr₁
  have hcover := s3_bottleneck_isCoveringMap p cc hcc hv hdeg huniq
  have hnear : ∀ z ∈ connectedComponentIn (Omega p) cc,
      p.eval z ∈ bottleneckSlit (p.eval cc) →
        ‖z - cc‖ < 4 / 3 * Real.sqrt (δ / ‖aHat‖) := fun z hz hslit =>
    bottleneck_slit_preimage_near p cc hcrit hv hcover aHat haHat h hh hdisk δ hδ
      hδpos hδsmall b₁ b₂ hb₁ hb₂ hr₁ hr₂ hzeros huniq z hz hslit
  have hD₁open : IsOpen (connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
    (bottleneckSlitDomain_isOpen p cc hv).connectedComponentIn
  have hb₁D : b₁ ∈ bottleneckSlitDomain p cc :=
    bottleneck_root_mem_slitDomain p cc b₁ hv hb₁ hr₁
  have hb₂D : b₂ ∈ bottleneckSlitDomain p cc :=
    bottleneck_root_mem_slitDomain p cc b₂ hv hb₂ hr₂
  -- The components of the two roots are disjoint.
  have hdisj : Disjoint (connectedComponentIn (bottleneckSlitDomain p cc) b₁)
      (connectedComponentIn (bottleneckSlitDomain p cc) b₂) := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    have heq₁ : connectedComponentIn (bottleneckSlitDomain p cc) b₁ =
        connectedComponentIn (bottleneckSlitDomain p cc) z := connectedComponentIn_eq hz₁
    have heq₂ : connectedComponentIn (bottleneckSlitDomain p cc) b₂ =
        connectedComponentIn (bottleneckSlitDomain p cc) z := connectedComponentIn_eq hz₂
    have hb₂D₁ : b₂ ∈ connectedComponentIn (bottleneckSlitDomain p cc) b₁ := by
      rw [heq₁, ← heq₂]
      exact mem_connectedComponentIn hb₂D
    exact bottleneck_preconnected_not_both_roots p cc hv hcover b₁ b₂ hne hr₁ hr₂
      _ isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (mem_connectedComponentIn hb₁D) hb₂D₁
  -- Radial images of the two sheets.
  have himg₁ : Set.Ico (4 / 3 * Real.sqrt (δ / ‖aHat‖)) ‖b₁ - cc‖ ⊆
      (fun z : ℂ => dist z cc) ''
        (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁) := by
    intro r hr
    obtain ⟨z, hz, hzr⟩ := bottleneck_sheet_crossing p cc hv hcover b₁ b₂ hne hr₁ hr₂
      hb₁ _ hnear K hK hKsub hK₁ hK₂ r hr
    exact ⟨z, hz, (dist_eq_norm z cc).trans hzr⟩
  have himg₂ : Set.Ico (4 / 3 * Real.sqrt (δ / ‖aHat‖)) ‖b₂ - cc‖ ⊆
      (fun z : ℂ => dist z cc) ''
        (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₂) := by
    intro r hr
    obtain ⟨z, hz, hzr⟩ := bottleneck_sheet_crossing p cc hv hcover b₂ b₁ hne.symm
      hr₂ hr₁ hb₂ _ hnear K hK hKsub hK₂ hK₁ r hr
    exact ⟨z, hz, (dist_eq_norm z cc).trans hzr⟩
  have hm₁ : ENNReal.ofReal (‖b₁ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤
      μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁) := by
    rw [← Real.volume_Ico]
    exact (measure_mono himg₁).trans (volume_dist_image_le_hausdorff cc _)
  have hm₂ : ENNReal.ofReal (‖b₂ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) ≤
      μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₂) := by
    rw [← Real.volume_Ico]
    exact (measure_mono himg₂).trans (volume_dist_image_le_hausdorff cc _)
  have hsplit : μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁) +
      μH[1] (K \ connectedComponentIn (bottleneckSlitDomain p cc) b₁) = μH[1] K :=
    measure_inter_add_diff K hD₁open.measurableSet
  have hdiff : μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₂) ≤
      μH[1] (K \ connectedComponentIn (bottleneckSlitDomain p cc) b₁) := by
    apply measure_mono
    intro z hz
    exact ⟨hz.1, fun hz₁ => Set.disjoint_left.mp hdisj hz₁ hz.2⟩
  calc ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      = ENNReal.ofReal ((‖b₁ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) +
          (‖b₂ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖))) := by
        congr 1
        ring
    _ ≤ ENNReal.ofReal (‖b₁ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) +
          ENNReal.ofReal (‖b₂ - cc‖ - 4 / 3 * Real.sqrt (δ / ‖aHat‖)) :=
        ENNReal.ofReal_add_le
    _ ≤ μH[1] (K ∩ connectedComponentIn (bottleneckSlitDomain p cc) b₁) +
          μH[1] (K \ connectedComponentIn (bottleneckSlitDomain p cc) b₁) :=
        add_le_add hm₁ (hm₂.trans hdiff)
    _ = μH[1] K := hsplit

/-! ## The instance `f` -/

/-- Every preconnected subset of the strict lemniscate of `f` that contains two
distinct roots has one-dimensional Hausdorff measure greater than two. -/
theorem erdos1041_counterexample_hausdorff :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K := by
  obtain ⟨zs, b₃, b₆, aHat, h, hzs_mem, hzs_crit, -, hzs_uniq,
      hv_pos, hδ_pos, hδ_le, haHat, hh, haHat_lo, hdisk, hδ_small,
      hzs_near, hb₃_root, hb₆_root, hb_ne, hb₃_near, hb₆_near,
      hroot_near, hb₃_uniq, hb₆_uniq, hproj⟩ := s4_instance_critical
  obtain ⟨g₁, g₂, hg₁cont, hg₂cont, hg₁zero, hg₂zero,
      hg₁zs, hg₂zs, hg₁pos, hg₂pos⟩ := s7_barriers zs hzs_near
  have hzeros : ∀ w ∈ connectedComponentIn (Omega f) zs,
      f.IsRoot w → w = b₃ ∨ w = b₆ := by
    intro w hw hwroot
    obtain ⟨j, hnear⟩ := hroot_near w hwroot
    by_cases hj3 : j.val = 3
    · left
      apply hb₃_uniq w hwroot
      simpa only [hj3, AssemblyAux.u_three] using hnear
    by_cases hj6 : j.val = 6
    · right
      apply hb₆_uniq w hwroot
      simpa only [hj6, AssemblyAux.u_six] using hnear
    have hjlt : j.val < 7 := j.isLt
    have hjother : (j.val = 0 ∨ j.val = 1 ∨ j.val = 2) ∨
        (j.val = 4 ∨ j.val = 5) := by omega
    rcases hjother with hjleft | hjright
    · exact False.elim
        (AssemblyAux.barrier_excludes f zs w hzs_mem hw g₁
          hg₁cont hg₁zero hg₁zs (hg₁pos j hjleft w hnear))
    · exact False.elim
        (AssemblyAux.barrier_excludes f zs w hzs_mem hw g₂
          hg₂cont hg₂zero hg₂zs (hg₂pos j hjright w hnear))
  obtain ⟨hb₃_mem, hb₆_mem⟩ :=
    s5_roots_connected_to_critical zs b₃ b₆ hzs_mem hzs_crit hb₃_root hb₆_root
      hb₃_near hb₆_near
  have huniq : ∀ c' ∈ connectedComponentIn (Omega f) zs,
      (Polynomial.derivative f).IsRoot c' → c' = zs := by
    intro c' hc' hcrit
    exact hzs_uniq c' (connectedComponentIn_subset (Omega f) zs hc') hcrit
  have hv : f.eval zs ≠ 0 := norm_pos_iff.mp hv_pos
  have hsqrt : Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) ≤
      (ρ : ℝ) * (ε : ℝ) / 5000 :=
    AssemblyAux.sqrt_le_scaled AssemblyAux.rho_pos AssemblyAux.epsilon_pos
      hδ_le haHat_lo
  have hloss : (8 / 3 : ℝ) * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) ≤
      8 / 3 * ((ρ : ℝ) * (ε : ℝ) / 5000) :=
    mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have hreal : (2 : ℝ) < ‖b₃ - zs‖ + ‖b₆ - zs‖ -
      8 / 3 * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) :=
    lt_of_lt_of_le AssemblyAux.rational_margin (sub_le_sub hproj hloss)
  have henn : (2 : ℝ≥0∞) < ENNReal.ofReal (‖b₃ - zs‖ + ‖b₆ - zs‖ -
      8 / 3 * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖)) := by
    have hpositive : 0 < ‖b₃ - zs‖ + ‖b₆ - zs‖ -
        8 / 3 * Real.sqrt ((1 - ‖f.eval zs‖) / ‖aHat‖) :=
      lt_trans (by norm_num) hreal
    simpa using (ENNReal.ofReal_lt_ofReal_iff hpositive).2 hreal
  intro z₁ z₂ hr₁ hr₂ hne K hK hz₁K hz₂K hKsub
  have hK_component : K ⊆ connectedComponentIn (Omega f) z₁ :=
    hK.subset_connectedComponentIn hz₁K hKsub
  have hz₁_mem : z₁ ∈ connectedComponentIn (Omega f) z₁ := hK_component hz₁K
  have hz₂_mem : z₂ ∈ connectedComponentIn (Omega f) z₁ := hK_component hz₂K
  have hz₁_Omega : z₁ ∈ Omega f := hKsub hz₁K
  have hdegree : 0 < f.natDegree := by
    rw [s4_f_monic_degree.2]
    norm_num
  obtain ⟨cc, hcc_mem, hcc_root⟩ :=
    s2_two_zeros_gives_critical_point f hdegree z₁ hz₁_Omega z₁ z₂ hz₁_mem hz₂_mem
      hne hr₁ hr₂
  have hcc_eq : cc = zs :=
    hzs_uniq cc (connectedComponentIn_subset (Omega f) z₁ hcc_mem) hcc_root
  have hzs_component : zs ∈ connectedComponentIn (Omega f) z₁ := by
    simpa only [hcc_eq] using hcc_mem
  have hcomponent : connectedComponentIn (Omega f) z₁ =
      connectedComponentIn (Omega f) zs := connectedComponentIn_eq hzs_component
  have hKzs : K ⊆ connectedComponentIn (Omega f) zs := by
    rw [← hcomponent]
    exact hK_component
  have hz₁_zs : z₁ ∈ connectedComponentIn (Omega f) zs := hKzs hz₁K
  have hz₂_zs : z₂ ∈ connectedComponentIn (Omega f) zs := hKzs hz₂K
  rcases hzeros z₁ hz₁_zs hr₁ with h13 | h16
  · rcases hzeros z₂ hz₂_zs hr₂ with h23 | h26
    · exact False.elim (hne (h13.trans h23.symm))
    · have hb₃K : b₃ ∈ K := by rw [← h13]; exact hz₁K
      have hb₆K : b₆ ∈ K := by rw [← h26]; exact hz₂K
      have hbound := s3_bottleneck_hausdorff f zs hzs_mem hzs_crit hv b₃ b₆ hb_ne
        hb₃_mem hb₆_mem hb₃_root hb₆_root hzeros huniq
        aHat haHat h hh hdisk (1 - ‖f.eval zs‖) rfl hδ_pos hδ_small
        K hK hKzs hb₃K hb₆K
      exact lt_of_lt_of_le henn hbound
  · rcases hzeros z₂ hz₂_zs hr₂ with h23 | h26
    · have hzeros_rev : ∀ w ∈ connectedComponentIn (Omega f) zs,
          f.IsRoot w → w = b₆ ∨ w = b₃ := by
        intro w hw hr
        exact (hzeros w hw hr).symm
      have hb₆K : b₆ ∈ K := by rw [← h16]; exact hz₁K
      have hb₃K : b₃ ∈ K := by rw [← h23]; exact hz₂K
      have hbound := s3_bottleneck_hausdorff f zs hzs_mem hzs_crit hv b₆ b₃ hb_ne.symm
        hb₆_mem hb₃_mem hb₆_root hb₃_root hzeros_rev huniq
        aHat haHat h hh hdisk (1 - ‖f.eval zs‖) rfl hδ_pos hδ_small
        K hK hKzs hb₆K hb₃K
      exact lt_of_lt_of_le henn (by simpa only [add_comm] using hbound)
    · exact False.elim (hne (h16.trans h26.symm))

/-! ## The Formal Conjectures parent, in its own vocabulary -/

/-- `Erdos1041.length` of Formal Conjectures, verbatim: the length of a subset
of `ℂ` is its one-dimensional Hausdorff measure. -/
noncomputable def fcLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- The image of a path joining two distinct roots of `f` inside `Ω(f)` has
Hausdorff length greater than two. -/
theorem erdos1041_path_range_hausdorff (z₁ z₂ : ℂ) (hr₁ : f.IsRoot z₁)
    (hr₂ : f.IsRoot z₂) (hne : z₁ ≠ z₂) (γ : Path z₁ z₂)
    (hsub : Set.range γ ⊆ {z : ℂ | ‖f.eval z‖ < 1}) :
    (2 : ℝ≥0∞) < fcLength (Set.range γ) :=
  erdos1041_counterexample_hausdorff z₁ z₂ hr₁ hr₂ hne (Set.range γ)
    (isPreconnected_range γ.continuous) ⟨0, γ.source⟩ ⟨1, γ.target⟩ hsub

-- The binder `h` below is unused, exactly as in the upstream statement this restates.
set_option linter.unusedVariables false in
/-- Negation of Formal Conjectures' `Erdos1041.erdos_1041`. Its section
variables `n`, `f`, `hn`, `hnum`, `h_monic`, `h` are quantified in their
declared order, and path length is `length (Set.range γ)`, the one-dimensional
Hausdorff measure of the image. The polynomial `f` of `Defs.lean` refutes it. -/
theorem erdos1041_hausdorff_negation :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2 := by
  intro huniv
  obtain ⟨hmonic, hdeg, hdisk, hnodup, -⟩ := erdos1041_counterexample
  have hn : (7 : ℕ) ≥ 2 := by norm_num
  have hrootset : f.rootSet ℂ ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    have hzroot : f.IsRoot z := by
      rw [IsRoot, ← coe_aeval_eq_eval]
      exact hmonic.mem_rootSet.mp hz
    simpa [mem_ball, dist_zero_right] using hdisk z hzroot
  obtain ⟨z₁, z₂, hle, γ, hsub, hlen⟩ := huniv 7 f hn hdeg hmonic hrootset
  have hz1_mem : z₁ ∈ f.roots := by
    have hpos : 0 < ({z₁, z₂} : Multiset ℂ).count z₁ := by
      simp [Multiset.count_singleton]
    exact Multiset.count_pos.mp
      (lt_of_lt_of_le hpos ((Multiset.le_iff_count.mp hle) z₁))
  have hz2_mem : z₂ ∈ f.roots := by
    have hpos : 0 < ({z₁, z₂} : Multiset ℂ).count z₂ := by
      simp [Multiset.count_cons]
    exact Multiset.count_pos.mp
      (lt_of_lt_of_le hpos ((Multiset.le_iff_count.mp hle) z₂))
  have hz1 : f.IsRoot z₁ := (mem_roots hmonic.ne_zero).mp hz1_mem
  have hz2 : f.IsRoot z₂ := (mem_roots hmonic.ne_zero).mp hz2_mem
  have hne : z₁ ≠ z₂ := by
    intro heq
    have htwo : 2 ≤ f.roots.count z₁ := by
      have hpair : ({z₁, z₂} : Multiset ℂ).count z₁ = 2 := by
        simp [heq]
      exact hpair ▸ (Multiset.le_iff_count.mp hle) z₁
    have hone : f.roots.count z₁ ≤ 1 :=
      (Multiset.nodup_iff_count_le_one.mp hnodup) z₁
    exact (Nat.not_succ_le_self 1) (le_trans htwo hone)
  exact lt_asymm (erdos1041_path_range_hausdorff z₁ z₂ hz1 hz2 hne γ hsub) hlen

set_option linter.unusedVariables false in
/-- The `answer(False) ↔ …` form of the same statement, which is how Formal
Conjectures records a question settled in the negative (`answer(False)`
elaborates to `False`). -/
theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2 :=
  ⟨False.elim, fun h => erdos1041_hausdorff_negation h⟩

end Erdos1041.Counterexample

#print axioms Erdos1041.Counterexample.erdos1041_counterexample_hausdorff
#print axioms Erdos1041.Counterexample.erdos1041_hausdorff_negation
#print axioms Erdos1041.Counterexample.erdos1041_hausdorff_answer_false
