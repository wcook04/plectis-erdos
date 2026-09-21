import ErdosProblems.Erdos249.FullDepthRayAmplifier
import Erdos249257.LcmConeFlatness

/-! Paper-form restatement of the long paper's simultaneous-certificate
proposition for Erdős #249: the existence of a function `f : ℕ → ℕ` with
`f(N) → ∞` such that

  `∀ N₀, ∃ N ≥ N₀, ∃ L, ∀ h ∈ {1,…,f(N)}, C(h,N,L)`

is equivalent to irrationality of `S`; under irrationality one may take
`f(N) = N+1`, and every `N` has a suitable depth.

Here `R_N = totientTail N`, `Δ_h(N) = shift h N = R_{N+h} - R_N` and
`C(h,N,L) = certifiedKill h N L`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.FullDepthRayAmplifier

/-! ### Distance from a real to the integers -/

/-- The distance from `x` to the nearest integer, written through the floor. -/
private noncomputable def intGap (x : ℝ) : ℝ :=
  min (x - (⌊x⌋ : ℝ)) ((⌊x⌋ : ℝ) + 1 - x)

private lemma intGap_pos {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    0 < intGap x := by
  have hgle : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have hglt : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
  have hne : x ≠ ((⌊x⌋ : ℤ) : ℝ) := fun h => hx ⟨⌊x⌋, h.symm⟩
  refine lt_min ?_ (by linarith)
  rcases lt_or_eq_of_le hgle with h | h
  · linarith
  · exact absurd h.symm hne

private lemma intGap_le_abs_sub (x : ℝ) (z : ℤ) : intGap x ≤ |x - (z : ℝ)| := by
  have hgle : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have hglt : x < ((⌊x⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one x
  by_cases hz : z ≤ ⌊x⌋
  · have hz' : ((z : ℤ) : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast hz
    have h1 : intGap x ≤ x - ((⌊x⌋ : ℤ) : ℝ) := min_le_left _ _
    have h2 : x - ((⌊x⌋ : ℤ) : ℝ) ≤ x - (z : ℝ) := by linarith
    exact (h1.trans h2).trans (le_abs_self _)
  · have hz1 : ⌊x⌋ + 1 ≤ z := Int.lt_iff_add_one_le.mp (not_le.mp hz)
    have hz' : ((⌊x⌋ : ℤ) : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz1
    have h1 : intGap x ≤ ((⌊x⌋ : ℤ) : ℝ) + 1 - x := min_le_right _ _
    have h2 : ((⌊x⌋ : ℤ) : ℝ) + 1 - x ≤ (z : ℝ) - x := by linarith
    calc intGap x ≤ (z : ℝ) - x := h1.trans h2
      _ ≤ |(z : ℝ) - x| := le_abs_self _
      _ = |x - (z : ℝ)| := abs_sub_comm _ _

/-! ### A depth beating a fixed separation -/

private lemma summable_affine_half (C : ℝ) :
    Summable (fun L : ℕ => (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L) := by
  have h1 : Summable (fun L : ℕ => C * (1 / 2 : ℝ) ^ L) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have h2 : Summable (fun L : ℕ => (L : ℝ) * (1 / 2 : ℝ) ^ L) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)
  exact (h1.add h2).congr fun L => by ring

private lemma exists_depth_small (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℕ, 2 * (C + (L : ℝ)) < δ * 2 ^ L := by
  have htend := (summable_affine_half C).tendsto_atTop_zero
  have hev : ∀ᶠ L : ℕ in Filter.atTop,
      (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L ∈ Set.Iio (δ / 2) :=
    htend.eventually_mem (Iio_mem_nhds (by positivity))
  obtain ⟨L, hL⟩ := hev.exists
  simp only [Set.mem_Iio] at hL
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hone : ((1 : ℝ) / 2) ^ L * 2 ^ L = 1 := by
    rw [← mul_pow]; norm_num
  have hmul := mul_lt_mul_of_pos_right hL h2L
  have hleft : (C + (L : ℝ)) * ((1 : ℝ) / 2) ^ L * 2 ^ L = C + (L : ℝ) := by
    rw [mul_assoc, hone, mul_one]
  rw [hleft] at hmul
  refine ⟨L, ?_⟩
  calc 2 * (C + (L : ℝ)) = (C + (L : ℝ)) * 2 := by ring
    _ < (δ / 2 * 2 ^ L) * 2 := by linarith
    _ = δ * 2 ^ L := by ring

/-! ### Simultaneous certificates with unrestricted depth -/

/-- **Every basepoint has a common depth.**  If `S` is irrational then, for
every `N` and every `M ≥ 1`, one depth `L` certifies all the shifts
`h ∈ {1,…,M}` at basepoint `N` simultaneously. -/
theorem exists_simultaneous_depth_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N M : ℕ)
    (hM : 1 ≤ M) :
    ∃ L, ∀ h ∈ Finset.Icc 1 M, certifiedKill h N L := by
  have hnon : ∀ h : ℕ, 0 < h → shift h N ∉ Set.range ((↑) : ℤ → ℝ) := by
    intro h hh
    simpa [shift] using
      irrational_totient_series_iff_all_tail_diffs_nonintegral.mp hS h hh N
  have hne : (Finset.Icc 1 M).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩⟩
  set δ := (Finset.Icc 1 M).inf' hne (fun h => intGap (shift h N)) with hδ
  obtain ⟨h₀, hh₀, hδeq⟩ :=
    Finset.exists_mem_eq_inf' hne (fun h => intGap (shift h N))
  have hδpos : 0 < δ := by
    rw [hδ, hδeq]
    exact intGap_pos (hnon h₀ (Finset.mem_Icc.mp hh₀).1)
  have hδle : ∀ h ∈ Finset.Icc 1 M, ∀ z : ℤ, δ ≤ |shift h N - (z : ℝ)| := by
    intro h hh z
    exact (Finset.inf'_le _ hh).trans (intGap_le_abs_sub _ z)
  obtain ⟨L, hL⟩ := exists_depth_small ((N : ℝ) + M + 2) hδpos
  refine ⟨L, ?_⟩
  intro h hh
  have hhM : (h : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hh).2
  refine certifiedKill_of_forall_dist ?_
  intro k
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have h3 : δ * 2 ^ L ≤ (2 : ℝ) ^ L * |shift h N - (k : ℝ)| := by
    have hb := mul_le_mul_of_nonneg_left (hδle h hh k) h2L.le
    rw [mul_comm δ ((2 : ℝ) ^ L)]
    exact hb
  linarith

/-- **`f(N) = N+1` works.**  Under irrationality every `N` has a depth `L`
certifying all the shifts `h ∈ {1,…,N+1}` at basepoint `N`. -/
theorem exists_simultaneous_depth_succ_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N : ℕ) :
    ∃ L, ∀ h ∈ Finset.Icc 1 (N + 1), certifiedKill h N L :=
  exists_simultaneous_depth_of_irrational hS N (N + 1) (by omega)

/-- **Simultaneous certificates with unrestricted depth.**  The existence of a
function `f : ℕ → ℕ` with `f(N) → ∞` such that
`∀ N₀, ∃ N ≥ N₀, ∃ L, ∀ h ∈ {1,…,f(N)}, C(h,N,L)`
is equivalent to irrationality of `S`. -/
theorem exists_growingShift_simultaneous_certificate_iff_irrational :
    (∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
        ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, ∀ h ∈ Finset.Icc 1 (f N),
          certifiedKill h N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · rintro ⟨f, hf, hcond⟩
    refine irrational_totient_series_of_certificate_supply ?_
    intro h hh N₀
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hf.eventually_ge_atTop h)
    obtain ⟨N, hN, L, hcert⟩ := hcond (max N₀ N₁)
    refine ⟨N, le_trans (le_max_left _ _) hN, L, ?_⟩
    exact hcert h
      (Finset.mem_Icc.mpr ⟨hh, hN₁ N (le_trans (le_max_right _ _) hN)⟩)
  · intro hS
    refine ⟨fun N => N + 1, ?_, ?_⟩
    · exact Filter.tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
    · intro N₀
      obtain ⟨L, hL⟩ := exists_simultaneous_depth_succ_of_irrational hS N₀
      exact ⟨N₀, le_rfl, L, hL⟩

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_of_irrational
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_succ_of_irrational
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_growingShift_simultaneous_certificate_iff_irrational
