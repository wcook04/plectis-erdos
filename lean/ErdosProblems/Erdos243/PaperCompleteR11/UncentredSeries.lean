import ErdosProblems.Erdos243.PaperCompleteR11.UncentredFinite

/-!
# Global uncentred record series

This module constructs the old-modulus supply from the actual LCM
state, including the alternative in which fresh steps cease. It proves the
mixed/raw equivalence for weights divergent on every arithmetic progression.
The real improper-integral specialisation is a separate analytic interface;
the progression-divergence assumption here is not a claim to discharge it.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR9 LcmRecordCrossing
open scoped BigOperators

/-- The exact discrete condition consumed by the global arithmetic proof. -/
def DivergesOnProgressions (f : ℕ → ℝ) : Prop :=
  ∀ x P : ℕ, 0 < P → ¬ Summable (fun k : ℕ ↦ f (x + k * P))

/-- Summable mixed charges would make every covered progression summable.
First crossings are constructed from unboundedness, not supplied as a budget. -/
theorem not_summable_mixed_of_cover
    (U rho : ℕ → ℕ) (a b L : ℕ → ℤ) (T x P B : ℕ)
    (hP : B < P) (hprefix : runningMax U T < x)
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n)
    (hstep : ∀ n, (rho n : ℤ) * U (n + 1) = a n * U n - b n * L n)
    (hcover : ∀ n, T ≤ n → rho n = 1 → ∀ k : ℕ, ∀ z : ℤ,
      ((x + k * P : ℕ) : ℤ) - B ≤ z → z < ((x + k * P : ℕ) : ℤ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L n ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiv : ¬ Summable (fun k : ℕ ↦ f (x + k * P))) :
    ¬ Summable (mixedCharge U rho B f) := by
  classical
  intro hsum
  apply hdiv
  apply summable_of_sum_le (fun k ↦ hpos (x + k * P))
  intro s
  obtain ⟨N, hN⟩ := hunbounded (s.sup (fun k ↦ x + k * P))
  have hfinite := finite_mixed_record_bound s U rho a b L T x P B N hP hprefix
    (fun k hk ↦ ⟨N, le_rfl, (Finset.le_sup hk).trans hN⟩)
    hstep hcover f hf hpos
  exact hfinite.trans (hsum.sum_le_tsum (Finset.range N)
    (fun n _ ↦ mixedCharge_nonneg U rho B f hpos n))

/-- Cofinal fresh steps supply a finite family of arbitrarily large,
pairwise-coprime old divisors. Only an eventual lower bound of two is required; an initial digit of one is allowed. -/
theorem fresh_steps_supply_old_moduli
    (q : ℕ) (a : ℕ → ℕ) (B : ℕ) (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n)
    (hcofinal : ∀ T : ℕ, ∃ n, T ≤ n ∧ lcmOverlap q a n = 1) :
    ∃ T : ℕ, ∃ m : Fin B → ℕ,
      (∀ i, B < m i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧
      (∀ i n, T ≤ n → m i ∣ cumulativeDigitLcm q a n) := by
  classical
  obtain ⟨Na, hNa⟩ := ha
  have hbig : ∀ T : ℕ, ∃ n, T ≤ n ∧ lcmOverlap q a n = 1 ∧ B < a n := by
    intro T
    obtain ⟨n, hn, hf⟩ := hcofinal (max Na (max T (smallDigitCutoff a B)))
    have hNaN : Na ≤ n := (Nat.le_max_left _ _).trans hn
    have hmid : max T (smallDigitCutoff a B) ≤ n := (Nat.le_max_right _ _).trans hn
    have hcut : smallDigitCutoff a B ≤ n := (Nat.le_max_right _ _).trans hmid
    refine ⟨n, (Nat.le_max_left _ _).trans hmid, hf, ?_⟩
    by_contra hnot
    have hd := small_digit_dvd_old_lcm q a B n hcut (by omega)
    have hdiv : a n ∣ lcmOverlap q a n := Nat.dvd_gcd hd (dvd_refl _)
    rw [hf] at hdiv
    have hle := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hdiv
    have han := hNa n hNaN
    omega
  let g : ℕ → ℕ := fun T ↦ Classical.choose (hbig T)
  have hg : ∀ T, T ≤ g T ∧ lcmOverlap q a (g T) = 1 ∧ B < a (g T) :=
    fun T ↦ Classical.choose_spec (hbig T)
  let j : ℕ → ℕ := Nat.rec (g 0) (fun _ prev ↦ g (prev + 1))
  have hjsucc : ∀ i, j (i + 1) = g (j i + 1) := fun _ ↦ rfl
  have hjmono : StrictMono j := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hjsucc]
    have hh := (hg (j i + 1)).1
    omega
  have hjfresh : ∀ i, lcmOverlap q a (j i) = 1 := by
    intro i
    cases i with
    | zero => exact (hg 0).2.1
    | succ i => exact (hg (j i + 1)).2.1
  have hjbig : ∀ i, B < a (j i) := by
    intro i
    cases i with
    | zero => exact (hg 0).2.2
    | succ i => exact (hg (j i + 1)).2.2
  refine ⟨j B + 1, (fun i ↦ a (j i.1)), (fun i ↦ hjbig i.1), ?_, ?_⟩
  · intro i k hik
    apply lcmFresh_coprime_of_ne q a _ (hjfresh i.1) (hjfresh k.1)
    intro heq
    exact hik (Fin.ext (hjmono.injective heq))
  · intro i n hn
    have hi := hjmono i.isLt
    exact digit_dvd_cumulativeDigitLcm_of_lt q a (by omega)

/-- The old covering required by the finite proof always exists: either
fresh steps cease, making its fresh-only condition vacuous, or CRT supplies
it from actual fresh digits. This is the global supplier, not a new premise. -/
theorem actual_lcm_covering
    (q : ℕ) (a U : ℕ → ℕ) (B : ℕ) (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n) :
    ∃ T x P : ℕ, B < P ∧ runningMax U T < x ∧
      ∀ n, T ≤ n → lcmOverlap q a n = 1 → ∀ k : ℕ, ∀ z : ℤ,
        ((x + k * P : ℕ) : ℤ) - B ≤ z → z < ((x + k * P : ℕ) : ℤ) →
        ∃ m : ℤ, (B : ℤ) < m ∧
          m ∣ (cumulativeDigitLcm q a n : ℤ) ∧ m ∣ z := by
  classical
  by_cases hcofinal : ∀ T : ℕ, ∃ n, T ≤ n ∧ lcmOverlap q a n = 1
  · obtain ⟨T, m, hm, hpair, hmOld⟩ :=
      fresh_steps_supply_old_moduli q a B ha hcofinal
    obtain ⟨x0, hBP, hx0, _hupper, hcover⟩ :=
      exists_crt_covering_progression m hm hpair
    let P : ℕ := ∏ i, m i
    let K : ℕ := runningMax U T + 1
    let x : ℕ := x0 + B + K * P
    have hP : B < P := hBP
    have hK : K ≤ K * P := by
      have h1 : 1 ≤ P := by omega
      simpa using Nat.mul_le_mul_left K h1
    have hx : runningMax U T < x := by dsimp [x, K] at *; omega
    refine ⟨T, x, P, hP, hx, ?_⟩
    intro n hn _hf k z hzlo hzhi
    have hwall : x + k * P = x0 + B + (K + k) * P := by dsimp [x]; ring
    rw [hwall] at hzlo hzhi
    exact hcover (cumulativeDigitLcm q a n)
      (fun i ↦ by exact_mod_cast hmOld i n hn) (K + k) z hzlo hzhi
  · push_neg at hcofinal
    obtain ⟨T, hT⟩ := hcofinal
    refine ⟨T, runningMax U T + 1, B + 1, by omega, by omega, ?_⟩
    intro n hn hf
    exact (hT n hn hf).elim

/-- Unbounded actual LCM height forces divergent mixed charge for every
fixed baseline. This is coefficient-uniform and has no centring condition. -/
theorem unbounded_not_summable_mixed
    (q : ℕ) (a U : ℕ → ℕ) (b : ℕ → ℤ) (B : ℕ)
    (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - b n * (cumulativeDigitLcm q a n : ℤ))
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiv : DivergesOnProgressions f) :
    ¬ Summable (mixedCharge U (lcmOverlap q a) B f) := by
  obtain ⟨T, x, P, hP, hx, hcover⟩ := actual_lcm_covering q a U B ha
  exact not_summable_mixed_of_cover U (lcmOverlap q a)
    (fun n ↦ (a n : ℤ)) b (fun n ↦ (cumulativeDigitLcm q a n : ℤ))
    T x P B hP hx hunbounded hstep hcover f hf hpos (hdiv x P (by omega))

/-- Bounded integer height has no late strict records. Repeated visits to a
height do not create new records, so boundedness really gives finite support. -/
theorem eventually_no_records_of_bounded
    (U : ℕ → ℕ) (hbounded : ∃ H : ℕ, ∀ n, U n ≤ H) :
    ∃ N : ℕ, ∀ n, N ≤ n → ¬ IsStrictRecord U n := by
  classical
  obtain ⟨H, hH⟩ := hbounded
  let N := smallDigitCutoff U H
  refine ⟨N, ?_⟩
  intro n hn hr
  have hex : ∃ j, U j = U (n + 1) := ⟨n + 1, rfl⟩
  have hspec : U (firstDigitIndex U (U (n + 1))) = U (n + 1) := by
    unfold firstDigitIndex
    rw [dif_pos hex]
    exact Nat.find_spec hex
  have hsum : firstDigitIndex U (U (n + 1)) ≤
      ∑ k ∈ Finset.range (H + 1), firstDigitIndex U k :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (by have hh := hH (n + 1); omega))
  have hi : firstDigitIndex U (U (n + 1)) ≤ n := by
    dsimp [N, smallDigitCutoff] at hn
    omega
  have hbad := hr _ hi
  omega

/-- A finite-prefix comparison avoids making an unjustified all-indices
claim when raw and mixed charges agree only above a height cutoff. -/
theorem summable_of_nonneg_of_eventual_le
    (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (hgs : Summable g) (hbound : ∃ N : ℕ, ∀ n, N ≤ n → f n ≤ g n) :
    Summable f := by
  classical
  obtain ⟨N, hN⟩ := hbound
  let e : ℕ → ℝ := fun n ↦ if n < N then f n else 0
  have he : Summable e := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    simp only [Finset.mem_range] at hn
    simp [e, hn]
  apply (hgs.add he).of_nonneg_of_le hf
  intro n
  by_cases hn : n < N
  · have hgn := hg n
    simp only [e, if_pos hn]
    linarith
  · simpa only [e, if_neg hn, add_zero] using hN n (by omega)

/-- Bounded height is equivalent to summability of mixed charge, for each
fixed baseline. The reverse direction constructs the required CRT supply. -/
theorem bounded_iff_summable_mixed
    (q : ℕ) (a U : ℕ → ℕ) (b : ℕ → ℤ) (B : ℕ)
    (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - b n * (cumulativeDigitLcm q a n : ℤ))
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiv : DivergesOnProgressions f) :
    (∃ H : ℕ, ∀ n, U n ≤ H) ↔
      Summable (mixedCharge U (lcmOverlap q a) B f) := by
  classical
  constructor
  · intro hb
    obtain ⟨N, hN⟩ := eventually_no_records_of_bounded U hb
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    have hn' : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    simp [mixedCharge, hN n hn']
  · intro hs
    by_contra hb
    have hu : ∀ H : ℕ, ∃ n, H ≤ U n := by
      intro H
      by_contra hn
      apply hb
      refine ⟨H, ?_⟩
      intro n
      have hh : ¬ H ≤ U n := fun h ↦ hn ⟨n, h⟩
      omega
    exact unbounded_not_summable_mixed q a U b B ha hstep hu f hf hpos hdiv hs

/-- The global raw-charge equivalence, without centring or coefficient
sign restrictions. The finitely many record endpoints below B are explicit. -/
theorem bounded_iff_summable_raw
    (q : ℕ) (a U : ℕ → ℕ) (b : ℕ → ℤ) (B : ℕ)
    (hq : 0 < q) (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - b n * (cumulativeDigitLcm q a n : ℤ))
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiv : DivergesOnProgressions f) :
    (∃ H : ℕ, ∀ n, U n ≤ H) ↔
      Summable (rawCharge U (lcmOverlap q a) B f) := by
  classical
  constructor
  · intro hb
    obtain ⟨N, hN⟩ := eventually_no_records_of_bounded U hb
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    have hn' : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    simp [rawCharge, hN n hn']
  · intro hs
    by_contra hb
    have hu : ∀ H : ℕ, ∃ n, H ≤ U n := by
      intro H
      by_contra hn
      apply hb
      refine ⟨H, ?_⟩
      intro n
      have hh : ¬ H ≤ U n := fun h ↦ hn ⟨n, h⟩
      omega
    obtain ⟨N, hN⟩ := hu B
    have hmixed : Summable (mixedCharge U (lcmOverlap q a) B f) := by
      apply summable_of_nonneg_of_eventual_le _ _
        (mixedCharge_nonneg _ _ _ _ hpos) (rawCharge_nonneg _ _ _ _ hpos) hs
      obtain ⟨Na, hNa⟩ := ha
      refine ⟨max N Na, ?_⟩
      intro n hn
      have han : 0 < a n := by have hh := hNa n (by omega); omega
      have hrhopos : 0 < lcmOverlap q a n := by
        unfold lcmOverlap
        rw [Nat.gcd_comm]
        exact Nat.gcd_pos_of_pos_left _ han
      apply mixedCharge_le_rawCharge U (lcmOverlap q a) B f hpos n
        (Nat.succ_le_of_lt hrhopos)
      intro hr
      exact hN.trans (le_of_lt (hr N (by omega)))
    exact unbounded_not_summable_mixed q a U b B ha hstep hu f hf hpos hdiv hmixed

/-- Mixed and raw charges have the same summability class for actual LCM
feedback, even though the two charges need not be asymptotically equal. -/
theorem mixed_summable_iff_raw_summable
    (q : ℕ) (a U : ℕ → ℕ) (b : ℕ → ℤ) (B : ℕ)
    (hq : 0 < q) (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - b n * (cumulativeDigitLcm q a n : ℤ))
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiv : DivergesOnProgressions f) :
    Summable (mixedCharge U (lcmOverlap q a) B f) ↔
      Summable (rawCharge U (lcmOverlap q a) B f) :=
  (bounded_iff_summable_mixed q a U b B ha hstep f hf hpos hdiv).symm.trans
    (bounded_iff_summable_raw q a U b B hq ha hstep f hf hpos hdiv)

end ErdosProblems.Erdos243.PaperCompleteR11
