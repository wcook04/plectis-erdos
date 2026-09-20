import Erdos249257.HalfCylinderSeamLimit
import ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies

/-!
Long Erdős #257 environment `thm:seam-limit` ("The quotient remainders converge
to the greedy deficit", `paper/reasoning-parts/erdos257/a257_front.tex`, line
2499), landed unconditionally.

`PaperCompleteR21/SeamQuotientDeficitLimit.lean` already proves the exact
quotient identity `X_{D_s}(2) = 1/2 - 2^{-s} - rem(s)/4^s + Φ_s/4^s`, the
window `0 ≤ Φ_s < s - 2`, `Φ_s/4^s → 0`, and the membership equivalence
`1/2 ∈ 𝒜 ↔ δ = 0`, but it leaves the whole environment conditional on one
missing input: the unconditional convergence

  `Tendsto seamGreedyFiniteValue atTop (nhds (X_G(2)))`, i.e. `X_{D_s}(2) → X_G(2)`.

This file proves that input and restates the environment unconditionally.  The
definitions and the downstream half of the argument are taken from
`SeamQuotientDeficitLimit.lean` (credited here; the names are fresh so the two
modules can coexist), and `PaperCompleteR21/GreedyOrbitNoTies.lean` supplies
`prop:one-orbit` in the form `approx_orbit_induction`.

The route is the paper's own.  Write `D_s` for the integer-greedy seam support
at row `s` and `G` for the real greedy support of `1/2`.

* The integer greedy on the weight list `seamWeights s` is read as a residual
  recursion (`listGreedyRemAfter`, `seamIntRem`), and after division by `4^s`
  it becomes exactly the abstract greedy rule `tailGreedyRemainder` applied to
  the scaled target `seamScaledTarget s = 1/2 - 2^{-s}` and the scaled weights
  `seamScaledWeight s d = ⌊4^s/(2^d-1)⌋ / 4^s`.
* `seamScaledTarget s → 1/2` and, for each fixed `d ≥ 1`,
  `seamScaledWeight s d → x_d`, with error at most `4^{-s}`.
* `approx_orbit_induction` (the inductive core of `prop:one-orbit`, which uses
  `lem:no-ties` at every rank) therefore gives, for each fixed `K`, the
  finite-prefix stability `D_s ∩ {1,…,K} = G ∩ {1,…,K}` for all large `s`.
* At such rows `|X_{D_s}(2) - X_G(2)| ≤ T_K = mersenneTail K`, and `T_K → 0`;
  letting `s → ∞` and then `K → ∞` gives convergence of the values.

Nothing here decides #257: the limit `δ = 1/2 - X_G(2) ≥ 0` is shown to exist,
and whether it is zero is exactly the open membership question.
-/

set_option autoImplicit false

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257
open Erdos249257.HalfCylinderIntegerGreedy
open Filter

/-! ## The descending integer greedy, read as a residual recursion -/

/-- In-range `List.getD` is `List.getElem`.  (`Mathlib.Data.List.GetD` is not in
this module's import closure, so the core `getD` normal form is used instead.) -/
theorem listGetD_eq_getElem {α : Type _} (l : List α) (d : α) {m : ℕ}
    (hm : m < l.length) : l.getD m d = l[m]'hm := by
  simp [List.getElem?_eq_getElem hm]

/-- The integer capacity remaining after the descending greedy of
`integerGreedyBits` has processed the first `m` weights of `ws`. -/
def listGreedyRemAfter : ℕ → List ℕ → ℕ → ℕ
  | 0, _, C => C
  | _ + 1, [], C => C
  | m + 1, w :: ws, C => listGreedyRemAfter m ws (if w ≤ C then C - w else C)

@[simp] theorem listGreedyRemAfter_zero (ws : List ℕ) (C : ℕ) :
    listGreedyRemAfter 0 ws C = C := rfl

theorem listGreedyRemAfter_cons (m w : ℕ) (ws : List ℕ) (C : ℕ) :
    listGreedyRemAfter (m + 1) (w :: ws) C
      = listGreedyRemAfter m ws (if w ≤ C then C - w else C) := rfl

/-- One step of the residual recursion, read at the far end of the prefix. -/
theorem listGreedyRemAfter_succ :
    ∀ (m : ℕ) (ws : List ℕ) (C : ℕ), m < ws.length →
      listGreedyRemAfter (m + 1) ws C
        = if ws.getD m 0 ≤ listGreedyRemAfter m ws C then
            listGreedyRemAfter m ws C - ws.getD m 0
          else listGreedyRemAfter m ws C := by
  intro m
  induction m with
  | zero =>
      intro ws C hm
      cases ws with
      | nil => simp at hm
      | cons w ws => simp [listGreedyRemAfter_cons]
  | succ m ih =>
      intro ws C hm
      cases ws with
      | nil => simp at hm
      | cons w ws =>
          have hm' : m < ws.length := by simpa using hm
          simpa [listGreedyRemAfter_cons, List.getD_cons_succ] using
            ih ws (if w ≤ C then C - w else C) hm'

/-- The bit the descending greedy writes at position `m` is exactly the
comparison of the `m`-th weight against the residual at that position. -/
theorem getD_integerGreedyBits :
    ∀ (m : ℕ) (ws : List ℕ) (C : ℕ), m < ws.length →
      (integerGreedyBits ws C).getD m false
        = decide (ws.getD m 0 ≤ listGreedyRemAfter m ws C) := by
  intro m
  induction m with
  | zero =>
      intro ws C hm
      cases ws with
      | nil => simp at hm
      | cons w ws =>
          rw [integerGreedyBits]
          by_cases h : w ≤ C
          · rw [if_pos h]
            simp [h]
          · rw [if_neg h]
            simp [h]
  | succ m ih =>
      intro ws C hm
      cases ws with
      | nil => simp at hm
      | cons w ws =>
          have hm' : m < ws.length := by simpa using hm
          rw [integerGreedyBits]
          by_cases h : w ≤ C
          · rw [if_pos h, List.getD_cons_succ, List.getD_cons_succ,
              listGreedyRemAfter_cons, if_pos h]
            exact ih ws (C - w) hm'
          · rw [if_neg h, List.getD_cons_succ, List.getD_cons_succ,
              listGreedyRemAfter_cons, if_neg h]
            exact ih ws C hm'

/-! ## Scaled seam coordinates -/

/-- The seam target `T_s = 2^{2s-1} - 2^s` on the quotient scale `4^s`. -/
noncomputable def seamScaledTarget (s : ℕ) : ℝ :=
  (seamSubsetTarget s : ℝ) / (4 : ℝ) ^ s

/-- The truncated integer weight `q(2s,d) = ⌊4^s/(2^d-1)⌋` on the quotient
scale `4^s`. -/
noncomputable def seamScaledWeight (s d : ℕ) : ℝ :=
  (truncatedMersenneWeight s d : ℝ) / (4 : ℝ) ^ s

/-- The integer residual of the seam greedy after its first `m` ranks. -/
def seamIntRem (s m : ℕ) : ℕ :=
  listGreedyRemAfter m (seamWeights s) (seamSubsetTarget s)

theorem seamIntRem_zero (s : ℕ) : seamIntRem s 0 = seamSubsetTarget s := rfl

theorem seamScaledTarget_eq {s : ℕ} (hs : 1 ≤ s) :
    seamScaledTarget s = 1 / 2 - (1 / 2 : ℝ) ^ s := by
  have hle : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((seamSubsetTarget s : ℕ) : ℝ)
      = (2 : ℝ) ^ (2 * s - 1) - (2 : ℝ) ^ s := by
    unfold seamSubsetTarget
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hbpos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have h4 : (4 : ℝ) ^ s = ((2 : ℝ) ^ s) ^ 2 := by
    rw [← pow_mul, mul_comm s 2, pow_mul]
    norm_num
  have hsq : (2 : ℝ) ^ (2 * s - 1) * 2 = ((2 : ℝ) ^ s) ^ 2 := by
    rw [← pow_succ, ← pow_mul]
    congr 1
    omega
  have ha : (2 : ℝ) ^ (2 * s - 1) = ((2 : ℝ) ^ s) ^ 2 / 2 := by linarith
  have hhalf : (1 / 2 : ℝ) ^ s = 1 / (2 : ℝ) ^ s := by
    rw [div_pow, one_pow]
  unfold seamScaledTarget
  rw [hcast, h4, ha, hhalf]
  have hne : ((2 : ℝ) ^ s) ≠ 0 := ne_of_gt hbpos
  field_simp

theorem tendsto_seamScaledTarget :
    Tendsto seamScaledTarget atTop (nhds (1 / 2 : ℝ)) := by
  have hpow : Tendsto (fun s : ℕ => (1 / 2 : ℝ) ^ s) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h : Tendsto (fun s : ℕ => 1 / 2 - (1 / 2 : ℝ) ^ s) atTop
      (nhds (1 / 2 - 0)) := tendsto_const_nhds.sub hpow
  have heq : (fun s : ℕ => 1 / 2 - (1 / 2 : ℝ) ^ s) =ᶠ[atTop] seamScaledTarget := by
    filter_upwards [eventually_ge_atTop 1] with s hs
    exact (seamScaledTarget_eq hs).symm
  simpa using Filter.Tendsto.congr' heq h

theorem four_pow_mul_seamScaledWeight (s d : ℕ) :
    (4 : ℝ) ^ s * seamScaledWeight s d
      = ((truncatedMersenneWeight s d : ℕ) : ℝ) := by
  have hne : ((4 : ℝ) ^ s) ≠ 0 := by positivity
  unfold seamScaledWeight
  field_simp

theorem seamScaledWeight_le_mersenneWeight (s : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    seamScaledWeight s d ≤ mersenneWeight d := by
  have hpos : (0 : ℝ) < (4 : ℝ) ^ s := by positivity
  have h := truncatedMersenneWeight_cast_le_scaled (s := s) hd
  refine le_of_mul_le_mul_left ?_ hpos
  rw [four_pow_mul_seamScaledWeight s d]
  exact h

theorem mersenneWeight_sub_seamScaledWeight_lt (s : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    mersenneWeight d - seamScaledWeight s d < (1 / 4 : ℝ) ^ s := by
  have hpos : (0 : ℝ) < (4 : ℝ) ^ s := by positivity
  have h := scaled_lt_truncatedMersenneWeight_cast_add_one (s := s) hd
  have hcast : (((truncatedMersenneWeight s d + 1 : ℕ) : ℕ) : ℝ)
      = ((truncatedMersenneWeight s d : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h
  have hprod : (4 : ℝ) ^ s * (1 / 4 : ℝ) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt hpos)
  rw [hprod, mul_sub, four_pow_mul_seamScaledWeight s d]
  linarith

theorem tendsto_seamScaledWeight {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun s : ℕ => seamScaledWeight s d) atTop (nhds (mersenneWeight d)) := by
  have hgeo : Tendsto (fun s : ℕ => (1 / 4 : ℝ) ^ s) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hdiff : Tendsto (fun s : ℕ => mersenneWeight d - seamScaledWeight s d)
      atTop (nhds 0) := by
    refine squeeze_zero (fun s => ?_) (fun s => ?_) hgeo
    · have := seamScaledWeight_le_mersenneWeight s hd
      linarith
    · exact (mersenneWeight_sub_seamScaledWeight_lt s hd).le
  have h : Tendsto
      (fun s : ℕ => mersenneWeight d - (mersenneWeight d - seamScaledWeight s d))
      atTop (nhds (mersenneWeight d - 0)) := tendsto_const_nhds.sub hdiff
  have heq : (fun s : ℕ => mersenneWeight d - (mersenneWeight d - seamScaledWeight s d))
      = fun s : ℕ => seamScaledWeight s d := by
    funext s
    ring
  rw [heq, sub_zero] at h
  exact h

/-! ## The scaled integer greedy is the abstract greedy rule -/

theorem seamWeights_getD {s m : ℕ} (hs : 2 ≤ s) (hm : m < s - 2) :
    (seamWeights s).getD m 0 = truncatedMersenneWeight s (m + 2) := by
  have hm' : m < (seamWeights s).length := by
    rw [seamWeights_length_eq]
    exact hm
  have h1 : (seamWeights s).getD m 0 = (seamWeights s)[m]'hm' :=
    listGetD_eq_getElem (seamWeights s) 0 hm'
  rw [h1]
  simp [seamWeights_eq_ofFn hs, List.getElem_ofFn]

theorem seamIntRem_succ {s m : ℕ} (hs : 2 ≤ s) (hm : m < s - 2) :
    seamIntRem s (m + 1)
      = if truncatedMersenneWeight s (m + 2) ≤ seamIntRem s m then
          seamIntRem s m - truncatedMersenneWeight s (m + 2)
        else seamIntRem s m := by
  have hm' : m < (seamWeights s).length := by
    rw [seamWeights_length_eq]
    exact hm
  unfold seamIntRem
  rw [listGreedyRemAfter_succ m (seamWeights s) (seamSubsetTarget s) hm',
    seamWeights_getD hs hm]

/-- The integer seam residual, divided by `4^s`, is exactly the abstract greedy
residual for the scaled target and the scaled weights. -/
theorem seamScaledRem_eq_tailGreedyRemainder {s : ℕ} (hs : 2 ≤ s) :
    ∀ m : ℕ, m ≤ s - 2 →
      ((seamIntRem s m : ℕ) : ℝ) / (4 : ℝ) ^ s
        = tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m := by
  intro m
  induction m with
  | zero =>
      intro _
      exact (tailGreedyRemainder_zero (seamScaledTarget s) (seamScaledWeight s)).symm
  | succ m ih =>
      intro hm
      have hmlt : m < s - 2 := by omega
      have ihm := ih (by omega)
      have hpos : (0 : ℝ) < (4 : ℝ) ^ s := by positivity
      have hidx : m + 1 + 1 = m + 2 := by omega
      have hwt : seamScaledWeight s (m + 2)
          = ((truncatedMersenneWeight s (m + 2) : ℕ) : ℝ) / (4 : ℝ) ^ s := rfl
      rw [seamIntRem_succ hs hmlt, tailGreedyRemainder_succ, hidx]
      by_cases hle : truncatedMersenneWeight s (m + 2) ≤ seamIntRem s m
      · have hcast : ((truncatedMersenneWeight s (m + 2) : ℕ) : ℝ)
            ≤ ((seamIntRem s m : ℕ) : ℝ) := by exact_mod_cast hle
        have hleR : seamScaledWeight s (m + 2)
            ≤ tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m := by
          rw [hwt, ← ihm]
          exact (div_le_div_iff_of_pos_right hpos).2 hcast
        rw [if_pos hle, if_pos hleR, ← ihm, hwt, Nat.cast_sub hle, sub_div]
      · have hcast : ¬ ((truncatedMersenneWeight s (m + 2) : ℕ) : ℝ)
            ≤ ((seamIntRem s m : ℕ) : ℝ) := by exact_mod_cast hle
        have hleR : ¬ (seamScaledWeight s (m + 2)
            ≤ tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m) := by
          rw [hwt, ← ihm]
          intro hcon
          exact hcast ((div_le_div_iff_of_pos_right hpos).1 hcon)
        rw [if_neg hle, if_neg hleR, ← ihm]

/-! ## The seam support, rank by rank -/

theorem mem_seamWordSupport_iff_bit {s d : ℕ} (h2 : 2 ≤ d) (_hd : d < s)
    (b : SeamRowWord s) (i : Fin (s - 2)) (hi : (i : ℕ) = d - 2) :
    d ∈ seamWordSupport b ↔ b i = true := by
  constructor
  · intro hmem
    obtain ⟨j, hj, hdj⟩ := mem_seamWordSupport_iff.mp hmem
    have hji : j = i := Fin.ext (by omega)
    rw [← hji]
    exact hj
  · intro hb
    refine mem_seamWordSupport_iff.mpr ⟨i, hb, ?_⟩
    omega

theorem seamGreedyWord_apply {s : ℕ} (i : Fin (s - 2)) :
    seamGreedyWord s i
      = (integerGreedyBits (seamWeights s) (seamSubsetTarget s)).getD (i : ℕ) false := by
  have hlist : (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
      = List.ofFn (seamGreedyWord s) := (seamGreedyWord_toList s).symm
  have hi : (i : ℕ) < (List.ofFn (seamGreedyWord s)).length := by
    simp
  rw [hlist, listGetD_eq_getElem (List.ofFn (seamGreedyWord s)) false hi]
  simp [List.getElem_ofFn]

theorem seamGreedyWord_eq_decide {s : ℕ} (hs : 2 ≤ s) (i : Fin (s - 2)) :
    seamGreedyWord s i
      = decide (truncatedMersenneWeight s ((i : ℕ) + 2) ≤ seamIntRem s (i : ℕ)) := by
  have hlen : (i : ℕ) < (seamWeights s).length := by
    rw [seamWeights_length_eq]
    exact i.isLt
  unfold seamIntRem
  rw [seamGreedyWord_apply i,
    getD_integerGreedyBits (i : ℕ) (seamWeights s) (seamSubsetTarget s) hlen,
    seamWeights_getD hs i.isLt]

/-- Rank `d` lies in the integer-greedy seam support at row `s` exactly when the
scaled weight fits in the abstract greedy residual. -/
theorem mem_seamGreedySupport_iff_scaled {s d : ℕ} (hs : 2 ≤ s) (h2 : 2 ≤ d)
    (hd : d < s) :
    d ∈ seamWordSupport (seamGreedyWord s)
      ↔ seamScaledWeight s d
          ≤ tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) (d - 2) := by
  have hlt : d - 2 < s - 2 := by omega
  have hd2 : d - 2 + 2 = d := by omega
  have hbit := mem_seamWordSupport_iff_bit h2 hd (seamGreedyWord s)
    (⟨d - 2, hlt⟩ : Fin (s - 2)) rfl
  have hdec := seamGreedyWord_eq_decide hs (⟨d - 2, hlt⟩ : Fin (s - 2))
  have hval : ((⟨d - 2, hlt⟩ : Fin (s - 2)) : ℕ) = d - 2 := rfl
  rw [hval, hd2] at hdec
  have hwt : seamScaledWeight s d
      = ((truncatedMersenneWeight s d : ℕ) : ℝ) / (4 : ℝ) ^ s := rfl
  have hpos : (0 : ℝ) < (4 : ℝ) ^ s := by positivity
  rw [hbit, hdec, decide_eq_true_iff,
    ← seamScaledRem_eq_tailGreedyRemainder hs (d - 2) (by omega), hwt]
  constructor
  · intro h
    exact (div_le_div_iff_of_pos_right hpos).2 (by exact_mod_cast h)
  · intro h
    exact_mod_cast (div_le_div_iff_of_pos_right hpos).1 h

/-! ## Finite-prefix stability (`prop:one-orbit`) at the seam -/

theorem one_not_mem_greedyHalfSupport :
    (1 : ℕ) ∉ greedyMersenneSupport (1 / 2 : ℝ) := by
  intro hmem
  have h : mersenneWeight 1 ≤ greedyMersenneRemainder (1 / 2 : ℝ) 0 := hmem.2
  rw [greedyMersenneRemainder_zero] at h
  have hw : mersenneWeight 1 = 1 := by norm_num [mersenneWeight]
  rw [hw] at h
  linarith

/-- Long `thm:seam-limit`, finite-prefix stability step.  For each fixed `K`,
the integer-greedy seam support and the real greedy support of `1/2` agree on
the ranks `1, …, K` at every sufficiently large row.  This is the seam instance
of `prop:one-orbit`. -/
theorem eventually_seamSupport_agrees (K : ℕ) :
    ∀ᶠ s in atTop, ∀ d : ℕ, 1 ≤ d → d ≤ K →
      (d ∈ seamWordSupport (seamGreedyWord s)
        ↔ d ∈ greedyMersenneSupport (1 / 2 : ℝ)) := by
  have hstab := (approx_orbit_induction seamScaledTarget seamScaledWeight
      tendsto_seamScaledTarget
      (fun n _ => tendsto_seamScaledWeight (d := n) (by omega)) K).2
  filter_upwards [hstab, eventually_ge_atTop (K + 3)] with s hsj hsK
  intro d h1 hdK
  have hs2 : 2 ≤ s := by omega
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · have hdeq : d = 1 := by omega
    subst hdeq
    constructor
    · intro hmem
      exact absurd (seamWordSupport_below hmem).1 (by omega)
    · intro hmem
      exact absurd hmem one_not_mem_greedyHalfSupport
  · have hds : d < s := by omega
    rw [mem_seamGreedySupport_iff_scaled hs2 hd2 hds, hsj d hd2 (by omega)]
    constructor
    · intro h
      exact ⟨by omega, h⟩
    · intro h
      exact h.2

/-! ## From prefix agreement to convergence of the values -/

theorem abs_supportValue_sub_le_mersenneTail {A B : Set ℕ} {K : ℕ}
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ K → (d ∈ A ↔ d ∈ B)) :
    |positiveMersenneSupportValue A - positiveMersenneSupportValue B|
      ≤ mersenneTail K := by
  classical
  have hA := positiveMersenneSupportValue_eq_prefix_add_suffix A K
  have hB := positiveMersenneSupportValue_eq_prefix_add_suffix B K
  have hsum : (∑ k ∈ Finset.range K, Set.indicator A mersenneWeight (k + 1))
      = ∑ k ∈ Finset.range K, Set.indicator B mersenneWeight (k + 1) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkK : k < K := Finset.mem_range.mp hk
    have hiff := h (k + 1) (by omega) (by omega)
    by_cases hmem : (k + 1) ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.1 hmem)]
    · rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (fun hc => hmem (hiff.2 hc))]
  have hdiff : positiveMersenneSupportValue A - positiveMersenneSupportValue B
      = positiveMersenneSupportSuffix A K - positiveMersenneSupportSuffix B K := by
    rw [hA, hB, hsum]
    ring
  rw [hdiff, abs_sub_le_iff]
  have hA1 := positiveMersenneSupportSuffix_le_tail A K
  have hA0 := positiveMersenneSupportSuffix_nonneg A K
  have hB1 := positiveMersenneSupportSuffix_le_tail B K
  have hB0 := positiveMersenneSupportSuffix_nonneg B K
  exact ⟨by linarith, by linarith⟩

/-- `X_G(2)`: the value of the real greedy support for the half target.
Definition taken from `PaperCompleteR21/SeamQuotientDeficitLimit.lean`. -/
noncomputable def greedyHalfTargetValue : ℝ :=
  positiveMersenneSupportValue (greedyMersenneSupport (1 / 2 : ℝ))

/-- The paper's `δ = 1/2 - X_G(2)`.  Taken from
`PaperCompleteR21/SeamQuotientDeficitLimit.lean`. -/
noncomputable def seamGreedyLimitDeficit : ℝ := 1 / 2 - greedyHalfTargetValue

/-- **The missing input of `thm:seam-limit`, proved.**  The finite seam values
converge to the value of the real greedy support of `1/2`:
`X_{D_s}(2) → X_G(2)`. -/
theorem tendsto_seamGreedyFiniteValue_greedyHalfTargetValue :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ : ∃ K : ℕ, mersenneTail K < ε :=
    (tendsto_mersenneTail_zero.eventually (gt_mem_nhds hε)).exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_seamSupport_agrees K)
  refine ⟨N, fun s hs => ?_⟩
  have hagree := hN s hs
  have hbound : |seamGreedyFiniteValue s - greedyHalfTargetValue|
      ≤ mersenneTail K := by
    unfold seamGreedyFiniteValue greedyHalfTargetValue
    refine abs_supportValue_sub_le_mersenneTail ?_
    intro d h1 hdK
    simpa using hagree d h1 hdK
  rw [Real.dist_eq]
  linarith

/-! ## The environment, unconditionally

The remaining pieces are those of
`PaperCompleteR21/SeamQuotientDeficitLimit.lean`, reproduced here under fresh
names so that the two modules can be imported together. -/

theorem half_mem_iff_greedyHalfTargetValue_eq :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ greedyHalfTargetValue = 1 / 2 := by
  constructor
  · rintro ⟨A, hA0, hv⟩
    have h : greedyMersenneSupport (1 / 2 : ℝ) = A := by
      rw [hv, greedySupport_supportValue_eq A hA0]
    rw [greedyHalfTargetValue, h, ← hv]
  · intro h
    unfold greedyHalfTargetValue at h
    exact ⟨greedyMersenneSupport (1 / 2 : ℝ), zero_not_mem_greedyMersenneSupport _, h.symm⟩

theorem half_mem_iff_seamGreedyLimitDeficit_eq_zero :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ seamGreedyLimitDeficit = 0 := by
  rw [half_mem_iff_greedyHalfTargetValue_eq, seamGreedyLimitDeficit]
  constructor <;> intro h <;> linarith

/-- The paper's `0 ≤ Φ_s < s - 2`. -/
theorem seamGreedyFloorError_window {s : ℕ} (hs : 3 ≤ s) :
    0 ≤ seamGreedyFloorError s ∧ seamGreedyFloorError s < ((s - 2 : ℕ) : ℚ) :=
  ⟨seamWordFloorError_nonneg (seamGreedyWord s),
    seamWordFloorError_lt_width hs (seamGreedyWord s)⟩

private theorem half_pow_eq_two_div_four (s : ℕ) :
    (1 / 2 : ℝ) ^ s = (2 : ℝ) ^ s / (4 : ℝ) ^ s := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, div_pow, one_pow]
  have h2 : ((2 : ℝ) ^ s) ≠ 0 := by positivity
  field_simp

/-- The paper's exact quotient identity
`X_{D_s}(2) = 1/2 - 2^{-s} - rem(s)/4^s + Φ_s/4^s`, solved for the normalised
quotient remainder. -/
theorem seamGreedyNormalizedRemainder_identity (s : ℕ) (hs : 5 ≤ s) :
    seamGreedyNormalizedRemainder s
      = 1 / 2 - (1 / 2 : ℝ) ^ s - seamGreedyFiniteValue s
        + ((seamGreedyFloorError s : ℚ) : ℝ) / (4 : ℝ) ^ s := by
  have hcast : ((seamWordRationalRemainder (seamGreedyWord s) : ℚ) : ℝ)
      = 1 / 2 - seamGreedyFiniteValue s := by
    rw [seamWordRationalRemainder, seamGreedyFiniteValue_eq_cast_rationalSum]
    push_cast
    rfl
  have hrem := seamWordRationalRemainder_eq_pow_add_floorZ_div (by omega : 1 ≤ s)
    (seamGreedyWord s)
  change seamWordRationalRemainder (seamGreedyWord s)
    = ((2 : ℚ) ^ s + seamGreedyFloorZ s) / (4 : ℚ) ^ s at hrem
  rw [seamGreedyFloorZ_eq_remainder_sub_error s hs] at hrem
  have hkey : (1 : ℝ) / 2 - seamGreedyFiniteValue s
      = ((2 : ℝ) ^ s + (seamIntegerGreedyRemainder s : ℝ)
          - ((seamGreedyFloorError s : ℚ) : ℝ)) / (4 : ℝ) ^ s := by
    rw [← hcast, hrem]
    push_cast
    ring
  unfold seamGreedyNormalizedRemainder
  linear_combination -hkey + half_pow_eq_two_div_four s

/-- The floor-error correction is negligible on the quotient scale. -/
theorem tendsto_seamGreedyFloorError_scaled_zero :
    Tendsto (fun s : ℕ => ((seamGreedyFloorError s : ℚ) : ℝ) / (4 : ℝ) ^ s)
      atTop (nhds 0) := by
  have hpow : Tendsto (fun s : ℕ => (1 / 2 : ℝ) ^ s) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine squeeze_zero' ?_ ?_ hpow
  · filter_upwards [eventually_ge_atTop 3] with s hs
    have h0 : (0 : ℝ) ≤ ((seamGreedyFloorError s : ℚ) : ℝ) := by
      exact_mod_cast (seamGreedyFloorError_window hs).1
    positivity
  · filter_upwards [eventually_ge_atTop 3] with s hs
    have hWR : ((seamGreedyFloorError s : ℚ) : ℝ) < ((s - 2 : ℕ) : ℝ) := by
      exact_mod_cast (seamGreedyFloorError_window hs).2
    have hnat : (s - 2 : ℕ) < 2 ^ s := lt_of_le_of_lt (Nat.sub_le s 2) Nat.lt_two_pow_self
    have hnatR : ((s - 2 : ℕ) : ℝ) < (2 : ℝ) ^ s := by exact_mod_cast hnat
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ s := by positivity
    rw [half_pow_eq_two_div_four s]
    exact (div_le_div_iff_of_pos_right h4pos).2 (le_of_lt (hWR.trans hnatR))

/-- The normalised quotient remainders converge to the greedy deficit. -/
theorem tendsto_seamGreedyNormalizedRemainder :
    Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit) := by
  have htend := tendsto_seamGreedyFiniteValue_greedyHalfTargetValue
  have hpow : Tendsto (fun s : ℕ => (1 / 2 : ℝ) ^ s) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hcomb : Tendsto
      (fun s : ℕ => 1 / 2 - (1 / 2 : ℝ) ^ s - seamGreedyFiniteValue s
        + ((seamGreedyFloorError s : ℚ) : ℝ) / (4 : ℝ) ^ s)
      atTop (nhds (1 / 2 - 0 - greedyHalfTargetValue + 0)) :=
    ((tendsto_const_nhds.sub hpow).sub htend).add
      tendsto_seamGreedyFloorError_scaled_zero
  have heq : (fun s : ℕ => 1 / 2 - (1 / 2 : ℝ) ^ s - seamGreedyFiniteValue s
        + ((seamGreedyFloorError s : ℚ) : ℝ) / (4 : ℝ) ^ s)
      =ᶠ[atTop] seamGreedyNormalizedRemainder := by
    filter_upwards [eventually_ge_atTop 5] with s hs
    exact (seamGreedyNormalizedRemainder_identity s hs).symm
  have hfinal := Filter.Tendsto.congr' heq hcomb
  simpa [seamGreedyLimitDeficit] using hfinal

/-- **Long `thm:seam-limit`, unconditionally.**  `X_{D_s}(2) → X_G(2)`;
`rem(s)/4^s → δ := 1/2 - X_G(2) ≥ 0`; and `1/2 ∈ 𝒜` is equivalent both to the
full sequence `rem(s)/4^s` tending to zero and to the existence of a cofinal row
sequence along which it tends to zero. -/
theorem paper_seam_limit_unconditional :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue) ∧
      Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit) ∧
      seamGreedyLimitDeficit = 1 / 2 - greedyHalfTargetValue ∧
      0 ≤ seamGreedyLimitDeficit ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        Tendsto seamGreedyNormalizedRemainder atTop (nhds 0)) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        ∃ rows : ℕ → ℕ, SeamGreedyRemainderSubquadraticAlong rows) := by
  have hlim := tendsto_seamGreedyNormalizedRemainder
  have hnn : ∀ s : ℕ, 0 ≤ seamGreedyNormalizedRemainder s := by
    intro s
    unfold seamGreedyNormalizedRemainder
    positivity
  have hdelta : 0 ≤ seamGreedyLimitDeficit := ge_of_tendsto' hlim hnn
  refine ⟨tendsto_seamGreedyFiniteValue_greedyHalfTargetValue, hlim, rfl, hdelta,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro hmem
    have hz : seamGreedyLimitDeficit = 0 :=
      half_mem_iff_seamGreedyLimitDeficit_eq_zero.1 hmem
    rwa [hz] at hlim
  · intro h0
    exact half_mem_iff_seamGreedyLimitDeficit_eq_zero.2 (tendsto_nhds_unique hlim h0)
  · intro hmem
    have hz : seamGreedyLimitDeficit = 0 :=
      half_mem_iff_seamGreedyLimitDeficit_eq_zero.1 hmem
    rw [hz] at hlim
    exact ⟨id, tendsto_id, hlim⟩
  · rintro ⟨rows, hrows⟩
    exact half_mem_mersenneAchievementSet_of_subquadraticAlong rows hrows

#print axioms listGetD_eq_getElem
#print axioms listGreedyRemAfter_succ
#print axioms getD_integerGreedyBits
#print axioms seamScaledTarget_eq
#print axioms tendsto_seamScaledTarget
#print axioms seamScaledWeight_le_mersenneWeight
#print axioms mersenneWeight_sub_seamScaledWeight_lt
#print axioms tendsto_seamScaledWeight
#print axioms seamWeights_getD
#print axioms seamIntRem_succ
#print axioms seamScaledRem_eq_tailGreedyRemainder
#print axioms mem_seamWordSupport_iff_bit
#print axioms seamGreedyWord_apply
#print axioms seamGreedyWord_eq_decide
#print axioms mem_seamGreedySupport_iff_scaled
#print axioms one_not_mem_greedyHalfSupport
#print axioms eventually_seamSupport_agrees
#print axioms abs_supportValue_sub_le_mersenneTail
#print axioms tendsto_seamGreedyFiniteValue_greedyHalfTargetValue
#print axioms half_mem_iff_greedyHalfTargetValue_eq
#print axioms half_mem_iff_seamGreedyLimitDeficit_eq_zero
#print axioms seamGreedyFloorError_window
#print axioms seamGreedyNormalizedRemainder_identity
#print axioms tendsto_seamGreedyFloorError_scaled_zero
#print axioms tendsto_seamGreedyNormalizedRemainder
#print axioms paper_seam_limit_unconditional

end ErdosProblems.Erdos257.PaperCompleteR21
