import ErdosProblems.Erdos1041.PaperAnalyticTargets
import Mathlib

/-!
# Erdős #1041: a path from a subcritical perimeter bound

Paper-form restatement of the environment of
`paper/reasoning-parts/erdos1041/core.tex` labelled `res:conjecture-p-consumer`
(line 1107).

The paper's proof runs in three stages.

1. `f` is proper and unramified, hence univalent, on each component of
   `{|f| < μ}` (the component-wise Riemann–Hurwitz count in the proof of
   `eks2010` Proposition 2.1); the inverse branch extends continuously to the
   closed disc at a critical boundary value; lower semicontinuity of length
   under uniform convergence transports the subcritical perimeter hypothesis to
   the two components `U_a, U_b` meeting at the first critical point `c_*`.
2. A bounded rectifiable Jordan domain `U` joins any `a ∈ U` to any
   `c ∈ ∂U` inside `closure U` with length at most `H¹(∂U)/2`.
3. The two paths are concatenated.

Mathlib v4.29.1 carries none of the classical theorems behind 1 and 2 — there is
no Riemann mapping theorem, no proper-map degree theory for plane domains, and
no Jordan curve theorem.  They enter here as the two named hypotheses
`SubcriticalSplitExists` and `HalfPerimeterJoin`.  Stage 3, the concatenation,
and the elementary selection at the heart of stage 2 are proved in full:

* `connectedAtMost_trans` — concatenation of two closed-sublevel connectors,
  with the variation of the concatenation computed by `eVariationOn.union`.
* `connectedAtMost_symm` — reversal of a connector.
* `connectedAtMost_mono` — monotonicity in the length budget.
* `half_perimeter_selection` — the elementary core of stage 2: with
  `|u - v| ≤ length A'` and `length A + length A' ≤ H¹(∂U)`, one of the two
  candidate paths through `u` or `v` has length at most `H¹(∂U)/2`.
* `subcritical_perimeter_path`, `subcritical_perimeter_path_paper` — the
  theorem, the second stated with the paper's own hypotheses on `f`, `μ`, `β`.

`ConnectedAtMost` is the tree's closed-sublevel connector predicate from
`ErdosProblems.Erdos1041.PaperAnalyticTargets`: a continuous curve on `[0,2]`
with the prescribed endpoints, staying in `{|f| ≤ R}`, of bounded variation, and
with extended variation at most `ENNReal.ofReal L`.  "Rectifiable path of length
at most `L` inside `K_μ`" is exactly `ConnectedAtMost f μ L`.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Set MeasureTheory
open ErdosProblems.Erdos1041.PaperAnalyticTargets

/-- Enlarging the length budget of a closed-sublevel connector. -/
theorem connectedAtMost_mono {f : ℂ → ℂ} {R L L' : ℝ} {a b : ℂ}
    (h : ConnectedAtMost f R L a b) (hLL : L ≤ L') : ConnectedAtMost f R L' a b := by
  obtain ⟨γ, hc, hs, he, hin, hbv, hv⟩ := h
  exact ⟨γ, hc, hs, he, hin, hbv, hv.trans (ENNReal.ofReal_le_ofReal hLL)⟩

/-- Reversing a closed-sublevel connector. -/
theorem connectedAtMost_symm {f : ℂ → ℂ} {R L : ℝ} {a b : ℂ}
    (h : ConnectedAtMost f R L a b) : ConnectedAtMost f R L b a := by
  obtain ⟨γ, hc, hs, he, hin, hbv, hv⟩ := h
  have hmaps : MapsTo (fun t : ℝ => 2 - t) (Icc (0 : ℝ) 2) (Icc (0 : ℝ) 2) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hanti : AntitoneOn (fun t : ℝ => 2 - t) (Icc (0 : ℝ) 2) := by
    intro u _ v _ huv
    simp only
    linarith
  have hvar : eVariationOn (fun t : ℝ => γ (2 - t)) (Icc (0 : ℝ) 2)
      ≤ eVariationOn γ (Icc (0 : ℝ) 2) :=
    eVariationOn.comp_le_of_antitoneOn γ (fun t : ℝ => 2 - t) hanti hmaps
  refine ⟨fun t => γ (2 - t), ?_, ?_, ?_, ?_, ?_, hvar.trans hv⟩
  · exact hc.comp ((continuous_const.sub continuous_id).continuousOn) hmaps
  · norm_num [he]
  · norm_num [hs]
  · intro t ht
    exact hin (2 - t) (hmaps ht)
  · exact ne_of_lt (lt_of_le_of_lt (hvar.trans hv) ENNReal.ofReal_lt_top)

/-- **Concatenation.**  The paper's last step: "Concatenating the two paths gives
length at most ...".  The extended variation of the concatenation is the sum of
the two variations by `eVariationOn.union`. -/
theorem connectedAtMost_trans {f : ℂ → ℂ} {R L₁ L₂ : ℝ} {a c b : ℂ}
    (h₁ : ConnectedAtMost f R L₁ a c) (h₂ : ConnectedAtMost f R L₂ c b)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    ConnectedAtMost f R (L₁ + L₂) a b := by
  classical
  obtain ⟨γ₁, hc₁, hs₁, he₁, hin₁, hbv₁, hv₁⟩ := h₁
  obtain ⟨γ₂, hc₂, hs₂, he₂, hin₂, hbv₂, hv₂⟩ := h₂
  set γ : ℝ → ℂ := fun t => if t ≤ 1 then γ₁ (2 * t) else γ₂ (2 * t - 2) with hγdef
  have hval1 : ∀ t ∈ Icc (0 : ℝ) 1, γ t = γ₁ (2 * t) := by
    intro t ht
    simp only [hγdef, if_pos ht.2]
  have hval2 : ∀ t ∈ Icc (1 : ℝ) 2, γ t = γ₂ (2 * t - 2) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      simp only [hγdef, if_pos (le_refl (1 : ℝ))]
      norm_num [he₁, hs₂]
    · simp only [hγdef, if_neg (by linarith : ¬ t ≤ 1)]
  have hEq1 : EqOn γ (fun t => γ₁ (2 * t)) (Icc (0 : ℝ) 1) := fun t ht => hval1 t ht
  have hEq2 : EqOn γ (fun t => γ₂ (2 * t - 2)) (Icc (1 : ℝ) 2) := fun t ht => hval2 t ht
  have hmaps1 : MapsTo (fun t : ℝ => 2 * t) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 2) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmaps2 : MapsTo (fun t : ℝ => 2 * t - 2) (Icc (1 : ℝ) 2) (Icc (0 : ℝ) 2) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmono1 : MonotoneOn (fun t : ℝ => 2 * t) (Icc (0 : ℝ) 1) := by
    intro u _ v _ huv
    simp only
    linarith
  have hmono2 : MonotoneOn (fun t : ℝ => 2 * t - 2) (Icc (1 : ℝ) 2) := by
    intro u _ v _ huv
    simp only
    linarith
  have hIccUnion : Icc (0 : ℝ) 1 ∪ Icc (1 : ℝ) 2 = Icc (0 : ℝ) 2 :=
    Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
  have hcont1 : ContinuousOn γ (Icc (0 : ℝ) 1) := by
    refine ContinuousOn.congr ?_ hEq1
    exact hc₁.comp ((continuous_const.mul continuous_id).continuousOn) hmaps1
  have hcont2 : ContinuousOn γ (Icc (1 : ℝ) 2) := by
    refine ContinuousOn.congr ?_ hEq2
    exact hc₂.comp (((continuous_const.mul continuous_id).sub continuous_const).continuousOn)
      hmaps2
  have hcont : ContinuousOn γ (Icc (0 : ℝ) 2) := by
    rw [← hIccUnion]
    exact hcont1.union_of_isClosed hcont2 isClosed_Icc isClosed_Icc
  have hvar1 : eVariationOn γ (Icc (0 : ℝ) 1) ≤ ENNReal.ofReal L₁ := by
    rw [eVariationOn.congr hEq1]
    exact le_trans (eVariationOn.comp_le_of_monotoneOn γ₁ (fun t : ℝ => 2 * t) hmono1 hmaps1) hv₁
  have hvar2 : eVariationOn γ (Icc (1 : ℝ) 2) ≤ ENNReal.ofReal L₂ := by
    rw [eVariationOn.congr hEq2]
    exact le_trans
      (eVariationOn.comp_le_of_monotoneOn γ₂ (fun t : ℝ => 2 * t - 2) hmono2 hmaps2) hv₂
  have hvarsplit : eVariationOn γ (Icc (0 : ℝ) 2)
      = eVariationOn γ (Icc (0 : ℝ) 1) + eVariationOn γ (Icc (1 : ℝ) 2) := by
    rw [← hIccUnion]
    exact eVariationOn.union γ ⟨by simp, fun x hx => hx.2⟩ ⟨by simp, fun x hx => hx.1⟩
  have hvartot : eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal (L₁ + L₂) := by
    rw [hvarsplit, ENNReal.ofReal_add hL₁ hL₂]
    exact add_le_add hvar1 hvar2
  refine ⟨γ, hcont, ?_, ?_, ?_, ?_, hvartot⟩
  · rw [hval1 0 (by simp)]
    norm_num [hs₁]
  · rw [hval2 2 (by simp)]
    norm_num [he₂]
  · intro t ht
    by_cases hle : t ≤ 1
    · rw [hval1 t ⟨ht.1, hle⟩]
      exact hin₁ (2 * t) (hmaps1 ⟨ht.1, hle⟩)
    · rw [hval2 t ⟨(not_le.mp hle).le, ht.2⟩]
      exact hin₂ (2 * t - 2) (hmaps2 ⟨(not_le.mp hle).le, ht.2⟩)
  · exact ne_of_lt (lt_of_le_of_lt hvartot ENNReal.ofReal_lt_top)

/-- **The elementary selection behind the half-perimeter lemma.**  The paper
takes a line through `a` meeting `U` in an interval whose closure is `[u,v]`,
splits `∂U` into the two arcs `A` (containing `c`) and `A'` from `u` to `v`, and
writes the two candidate paths `a → u → c` and `a → v → c`.  With
`du + dv = |u - v|` (because `a` lies on `[u,v]`), `|u - v| ≤ length A'`, and
`length A + length A' ≤ H¹(∂U)`, where `length A = lenA1 + lenA2` splits `A` at
`c`, one of the two paths has length at most `H¹(∂U)/2`. -/
theorem half_perimeter_selection {du dv lenA1 lenA2 lenA' uv H : ℝ}
    (hsplit : du + dv = uv) (hchord : uv ≤ lenA')
    (htotal : lenA1 + lenA2 + lenA' ≤ H) :
    min (du + lenA1) (dv + lenA2) ≤ H / 2 := by
  have hsum : du + lenA1 + (dv + lenA2) ≤ H := by linarith
  rcases min_cases (du + lenA1) (dv + lenA2) with ⟨h, hle⟩ | ⟨h, hlt⟩
  · rw [h]; linarith
  · rw [h]; linarith

/-- The Jordan-domain half-perimeter property of a component `U` of a closed
sublevel set: any interior point is joined to any boundary point, inside the
sublevel set `{|f| ≤ R}`, by a rectifiable path of length at most half of
`H¹(∂U)`.  The paper calls this elementary; its proof selects one of the two
boundary arcs of a Jordan curve, which needs the Jordan curve theorem.  Mathlib
v4.29.1 has no Jordan curve theorem.  `connectedAtMost_half_perimeter` below
derives this property from the arc datum the Jordan curve supplies, so the only
external part is the existence of that datum. -/
def HalfPerimeterJoin (f : ℂ → ℂ) (R : ℝ) (U : Set ℂ) : Prop :=
  ∀ H : ℝ, μH[(1 : ℝ)] (frontier U) ≤ ENNReal.ofReal H →
    ∀ p ∈ U, ∀ q ∈ frontier U, ConnectedAtMost f R (H / 2) p q

/-- The datum the Jordan curve theorem supplies at an interior point `a` and a
boundary point `c` of a rectifiable Jordan domain `U` with `H¹(∂U) ≤ H`: a chord
`[u,v]` of `U` through `a` (so `|a - u| + |a - v| = |u - v|`, and both spokes lie
in `closure U`), the two sub-arcs of the boundary arc `A` from `u` and from `v`
to `c`, and the complementary boundary arc `A'`, which is at least as long as the
chord, with `length A + length A' ≤ H`. -/
def JordanArcDatum (f : ℂ → ℂ) (R H : ℝ) (a c : ℂ) : Prop :=
  ∃ (u v : ℂ) (lu lv la1 la2 la' : ℝ),
    0 ≤ lu ∧ 0 ≤ lv ∧ 0 ≤ la1 ∧ 0 ≤ la2 ∧
    ConnectedAtMost f R lu a u ∧ ConnectedAtMost f R lv a v ∧
    ConnectedAtMost f R la1 u c ∧ ConnectedAtMost f R la2 v c ∧
    lu + lv = ‖u - v‖ ∧ ‖u - v‖ ≤ la' ∧ la1 + la2 + la' ≤ H

/-- **The half-perimeter lemma, from the Jordan arc datum.**  The two candidate
paths `a → u → c` and `a → v → c` are built by concatenation and one of them has
length at most `H/2` by `half_perimeter_selection`. -/
theorem connectedAtMost_half_perimeter {f : ℂ → ℂ} {R H : ℝ} {a c : ℂ}
    (h : JordanArcDatum f R H a c) : ConnectedAtMost f R (H / 2) a c := by
  obtain ⟨u, v, lu, lv, la1, la2, la', hlu, hlv, hla1, hla2, hau, hav, huc, hvc,
    hchordsplit, hchord, htotal⟩ := h
  have hsel := half_perimeter_selection hchordsplit hchord htotal
  rcases min_cases (lu + la1) (lv + la2) with ⟨hmin, _⟩ | ⟨hmin, _⟩
  · rw [hmin] at hsel
    exact connectedAtMost_mono (connectedAtMost_trans hau huc hlu hla1) hsel
  · rw [hmin] at hsel
    exact connectedAtMost_mono (connectedAtMost_trans hav hvc hlv hla2) hsel

/-- The half-perimeter joining property of `U` follows from the Jordan arc datum
at every interior point and boundary point. -/
theorem halfPerimeterJoin_of_jordanArcDatum {f : ℂ → ℂ} {R : ℝ} {U : Set ℂ}
    (h : ∀ H : ℝ, μH[(1 : ℝ)] (frontier U) ≤ ENNReal.ofReal H →
      ∀ p ∈ U, ∀ q ∈ frontier U, JordanArcDatum f R H p q) :
    HalfPerimeterJoin f R U :=
  fun H hH p hp q hq => connectedAtMost_half_perimeter (h H hH p hp q hq)

/-- The classical input of stage 1: at the first critical level the sublevel set
carries two distinct one-root components `U_a`, `U_b` whose closures meet at a
critical point, each of perimeter at most `P`, and each with the half-perimeter
joining property.  This packages exactly the theorems Mathlib does not carry:
the component-wise Riemann–Hurwitz count of `eks2010` Proposition 2.1, the
continuous extension of the inverse branch through
`f(z) - f(c) = (z-c)^d h(z)`, lower semicontinuity of length under uniform
convergence, and the Jordan curve theorem behind `HalfPerimeterJoin`. -/
def SubcriticalSplitExists (f : ℂ → ℂ) (μ P : ℝ) : Prop :=
  ∃ (a b c : ℂ) (Ua Ub : Set ℂ), a ≠ b ∧ f a = 0 ∧ f b = 0 ∧
    a ∈ Ua ∧ b ∈ Ub ∧ c ∈ frontier Ua ∧ c ∈ frontier Ub ∧
    μH[(1 : ℝ)] (frontier Ua) ≤ ENNReal.ofReal P ∧
    μH[(1 : ℝ)] (frontier Ub) ≤ ENNReal.ofReal P ∧
    HalfPerimeterJoin f μ Ua ∧ HalfPerimeterJoin f μ Ub

/-- The paper's conclusion: two distinct roots joined inside `{|f| ≤ R}` by a
rectifiable path of length at most `L`. -/
def HasDistinctConnectionAtMost (f : ℂ → ℂ) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ f a = 0 ∧ f b = 0 ∧ ConnectedAtMost f R L a b

/-- **`res:conjecture-p-consumer`, assembly.**  Given the subcritical split at
the first critical level with perimeter budget `P`, two distinct roots are
joined inside `K_μ = {|f| ≤ μ}` by a rectifiable path of length at most `P`. -/
theorem subcritical_perimeter_path {f : ℂ → ℂ} {μ P : ℝ} (hP : 0 ≤ P)
    (hsplit : SubcriticalSplitExists f μ P) :
    HasDistinctConnectionAtMost f μ P := by
  obtain ⟨a, b, c, Ua, Ub, hab, hfa, hfb, haU, hbU, hca, hcb, hPa, hPb, hja, hjb⟩ := hsplit
  refine ⟨a, b, hab, hfa, hfb, ?_⟩
  have h1 : ConnectedAtMost f μ (P / 2) a c := hja P hPa a haU c hca
  have h2 : ConnectedAtMost f μ (P / 2) c b :=
    connectedAtMost_symm (hjb P hPb b hbU c hcb)
  have hhalf : (0 : ℝ) ≤ P / 2 := by linarith
  have := connectedAtMost_trans h1 h2 hhalf hhalf
  have hPP : P / 2 + P / 2 = P := by ring
  rwa [hPP] at this

set_option linter.unusedVariables false in
/-- **`res:conjecture-p-consumer`.**  The paper's statement with its own
hypotheses on `f`, `μ` and `β`: `f` squarefree monic of degree `n ≥ 2`,
`μ = min_{f'(c)=0}|f(c)| > 0`, and `β > 0` bounding `H¹(∂C)` by `β σ^{1/n}` for
every `0 < σ < μ` and every component `C` of `{|f| ≤ σ}`.  The passage from
those hypotheses to the two-component split at the first critical level is the
external input `hsplit`; everything after it is proved. -/
theorem subcritical_perimeter_path_paper
    (p : Polynomial ℂ) (n : ℕ) (μ β : ℝ)
    (hmonic : p.Monic) (hsf : Squarefree p) (hdeg : p.natDegree = n) (hn : 2 ≤ n)
    (hμ : CriticalMinimum p μ) (hμpos : 0 < μ) (hβ : 0 < β)
    (hperim : ∀ σ : ℝ, 0 < σ → σ < μ → ∀ z : ℂ, ‖p.eval z‖ ≤ σ →
      μH[(1 : ℝ)] (frontier (connectedComponentIn {w : ℂ | ‖p.eval w‖ ≤ σ} z))
        ≤ ENNReal.ofReal (β * σ ^ (1 / (n : ℝ))))
    (hsplit : SubcriticalSplitExists (fun z => p.eval z) μ (β * μ ^ (1 / (n : ℝ)))) :
    HasDistinctConnectionAtMost (fun z => p.eval z) μ (β * μ ^ (1 / (n : ℝ))) := by
  exact subcritical_perimeter_path (mul_nonneg hβ.le (Real.rpow_nonneg hμpos.le _)) hsplit

#print axioms connectedAtMost_mono
#print axioms connectedAtMost_symm
#print axioms connectedAtMost_trans
#print axioms half_perimeter_selection
#print axioms connectedAtMost_half_perimeter
#print axioms halfPerimeterJoin_of_jordanArcDatum
#print axioms subcritical_perimeter_path
#print axioms subcritical_perimeter_path_paper

end ErdosProblems.Erdos1041.PaperCompleteR21

end
