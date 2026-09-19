import ErdosProblems.Erdos243.PaperCompleteR11.CanonicalRecords
import ErdosProblems.Erdos243.LcmRecordExcess

/-!
# Exact abstract arithmetic weighted-record dichotomy

This file closes the abstract theorem printed as
`long243:res:arithmeticrecord`.  Unlike the earlier coefficient-uniform
LCM theorem, it does not assume that the digits are eventually at least two.
The paper's lower centring inequality is used exactly where it belongs:
every strict height record is a fresh LCM step.  Unboundedness then supplies
cofinally many such record steps, and those record digits themselves supply
the old CRT moduli.

The infinite record sum is represented as the nonnegative masked series
`paperRecordCharge`; this is exactly the paper sum over strict records.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR9 LcmRecordCrossing LcmRecordExcess
open scoped BigOperators

/-- An unbounded natural-valued sequence has strict record steps cofinally.
This permits arbitrary drawdowns between records. -/
theorem strict_records_cofinal_of_unbounded
    (U : ℕ → ℕ) (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n) :
    ∀ T : ℕ, ∃ n, T ≤ n ∧ IsStrictRecord U n := by
  intro T
  obtain ⟨j, hj⟩ := hunbounded (runningMax U T + 1)
  have hzero : U 0 < runningMax U T + 1 := by
    have hh := le_runningMax U (Nat.zero_le T)
    omega
  have hreach : ∃ k ≤ j, runningMax U T + 1 ≤ U k := ⟨j, le_rfl, hj⟩
  obtain ⟨n, hn, _huniq⟩ :=
    exists_unique_firstCrossing U (runningMax U T + 1) j hzero hreach
  have hnT : T ≤ n := by
    by_contra hnot
    have hnt : n < T := by omega
    have hle : U (n + 1) ≤ runningMax U T :=
      le_runningMax U (by omega)
    have hhi := hn.2.2
    omega
  exact ⟨n, hnT, hn.2.is_record⟩

/-- Under the printed centring inequality every strict record is an LCM-fresh
step, and its actual source-to-endpoint jump is `-V`. -/
theorem strict_record_is_fresh_of_centering
    (q : ℕ) (a U : ℕ → ℕ) (V : ℕ → ℤ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n) (hU : ∀ n, 0 < U n)
    (hstate : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) = (U n : ℤ) - V n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n)
    {n : ℕ} (hr : IsStrictRecord U n) :
    lcmOverlap q a n = 1 ∧
      ((U (n + 1) : ℤ) - U n = -V n) := by
  have hrho : (1 : ℤ) ≤ (lcmOverlap q a n : ℤ) := by
    exact_mod_cast (Nat.succ_le_of_lt (lcmOverlap_pos hq ha n))
  have hrise : (U n : ℤ) < U (n + 1) := by
    exact_mod_cast (hr n le_rfl)
  have hh := rise_is_fresh
    (U := (U n : ℤ)) (U' := (U (n + 1) : ℤ))
    (V := V n) (rho := (lcmOverlap q a n : ℤ))
    (by exact_mod_cast hU n) hrho (hcenter n) (hstate n) hrise
  constructor
  · exact_mod_cast hh.1
  · exact hh.2

/-- Once every small digit that ever appears has entered the old LCM, a
fresh strict record digit must exceed the prescribed baseline.  The digit
`1` is excluded by the positive record jump and the exact centred error
identity, so no eventual `a_n ≥ 2` premise is needed. -/
theorem late_fresh_record_digit_large
    (q : ℕ) (a U : ℕ → ℕ) (V : ℕ → ℤ) (B n : ℕ)
    (hq : 0 < q) (ha : ∀ j, 0 < a j) (hU : ∀ j, 0 < U j)
    (hstate : ∀ j, (lcmOverlap q a j : ℤ) * U (j + 1) = (U j : ℤ) - V j)
    (herror : ∀ j, V j = (cumulativeDigitLcm q a j : ℤ) -
      ((a j : ℤ) - 1) * U j)
    (hcenter : ∀ j, -(U j : ℤ) ≤ 2 * V j)
    (hn : smallDigitCutoff a B ≤ n) (hr : IsStrictRecord U n) :
    B < a n := by
  obtain ⟨hfresh, hjump⟩ := strict_record_is_fresh_of_centering
    q a U V hq ha hU hstate hcenter hr
  by_contra hnot
  have hsmall : a n ≤ B := by omega
  have hdold := small_digit_dvd_old_lcm q a B n hn hsmall
  have hda : a n ∣ lcmOverlap q a n := Nat.dvd_gcd hdold (dvd_refl _)
  rw [hfresh] at hda
  have haone : a n = 1 := by
    have hle := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hda
    have hp := ha n
    omega
  have hLpos : 0 < cumulativeDigitLcm q a n := cumulativeDigitLcm_pos hq ha n
  have hVpos : (0 : ℤ) < V n := by
    rw [herror n, haone]
    norm_num
    exact_mod_cast hLpos
  have : (U n : ℤ) < U (n + 1) := by exact_mod_cast hr n le_rfl
  nlinarith

/-- On an unbounded centred orbit, the strict record digits themselves
supply any finite family of pairwise-coprime old moduli larger than `B`.
Every selected modulus remains in the cumulative LCM after the supply time. -/
theorem centred_record_steps_supply_old_moduli
    (q : ℕ) (a U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n) (hU : ∀ n, 0 < U n)
    (hstate : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) = (U n : ℤ) - V n)
    (herror : ∀ n, V n = (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * U n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n)
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n) :
    ∃ T : ℕ, ∃ m : Fin B → ℕ,
      (∀ i, B < m i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧
      (∀ i n, T ≤ n → m i ∣ cumulativeDigitLcm q a n) := by
  classical
  have hcofinal := strict_records_cofinal_of_unbounded U hunbounded
  let cutoff := smallDigitCutoff a B
  let g : ℕ → ℕ := fun T ↦ Classical.choose (hcofinal T)
  have hg : ∀ T, T ≤ g T ∧ IsStrictRecord U (g T) :=
    fun T ↦ Classical.choose_spec (hcofinal T)
  let j : ℕ → ℕ := Nat.rec (g cutoff) (fun _ prev ↦ g (prev + 1))
  have hjsucc : ∀ i, j (i + 1) = g (j i + 1) := fun _ ↦ rfl
  have hjmono : StrictMono j := by
    apply strictMono_nat_of_lt_succ
    intro i
    rw [hjsucc]
    have hh := (hg (j i + 1)).1
    omega
  have hjrecord : ∀ i, IsStrictRecord U (j i) := by
    intro i
    cases i with
    | zero => exact (hg cutoff).2
    | succ i => exact (hg (j i + 1)).2
  have hjcut : ∀ i, cutoff ≤ j i := by
    intro i
    induction i with
    | zero => exact (hg cutoff).1
    | succ i ih =>
        exact ih.trans (Nat.le_of_lt (hjmono (Nat.lt_succ_self i)))
  have hjfresh : ∀ i, lcmOverlap q a (j i) = 1 := by
    intro i
    exact (strict_record_is_fresh_of_centering q a U V hq ha hU hstate hcenter
      (hjrecord i)).1
  have hjbig : ∀ i, B < a (j i) := by
    intro i
    exact late_fresh_record_digit_large q a U V B (j i) hq ha hU hstate herror
      hcenter (hjcut i) (hjrecord i)
  refine ⟨j B + 1, (fun i ↦ a (j i.1)), (fun i ↦ hjbig i.1), ?_, ?_⟩
  · intro i k hik
    apply lcmFresh_coprime_of_ne q a _ (hjfresh i.1) (hjfresh k.1)
    intro heq
    exact hik (Fin.ext (hjmono.injective heq))
  · intro i n hn
    have hi : j i.1 < j B := hjmono i.isLt
    exact digit_dvd_cumulativeDigitLcm_of_lt q a (by omega)

/-- The selected record digits give one permanent CRT covering progression.
This is the exact old-modulus supplier used in the paper proof. -/
theorem centred_actual_lcm_covering
    (q : ℕ) (a U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n) (hU : ∀ n, 0 < U n)
    (hstate : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) = (U n : ℤ) - V n)
    (herror : ∀ n, V n = (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * U n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n)
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n) :
    ∃ T x P : ℕ, B < P ∧ runningMax U T < x ∧
      ∀ n, T ≤ n → ∀ k : ℕ, ∀ z : ℤ,
        ((x + k * P : ℕ) : ℤ) - B ≤ z → z < ((x + k * P : ℕ) : ℤ) →
        ∃ m : ℤ, (B : ℤ) < m ∧
          m ∣ (cumulativeDigitLcm q a n : ℤ) ∧ m ∣ z := by
  classical
  obtain ⟨T, m, hm, hpair, hmOld⟩ := centred_record_steps_supply_old_moduli
    q a U V B hq ha hU hstate herror hcenter hunbounded
  obtain ⟨x0, hBP, _hxlo, _hxhi, hcover⟩ :=
    exists_crt_covering_progression m hm hpair
  let P : ℕ := ∏ i, m i
  let K : ℕ := runningMax U T + 1
  let x : ℕ := x0 + B + K * P
  have hP : B < P := hBP
  have hK : K ≤ K * P := by
    have h1 : 1 ≤ P := by omega
    simpa using Nat.mul_le_mul_left K h1
  have hx : runningMax U T < x := by
    dsimp [x, K] at *
    omega
  refine ⟨T, x, P, hP, hx, ?_⟩
  intro n hn k z hzlo hzhi
  have hwall : x + k * P = x0 + B + (K + k) * P := by
    dsimp [x]
    ring
  rw [hwall] at hzlo hzhi
  exact hcover (cumulativeDigitLcm q a n)
    (fun i ↦ by exact_mod_cast hmOld i n hn) (K + k) z hzlo hzhi

/-- The paper's centring forces mixed and raw record charges to agree exactly:
on a strict record the overlap is one, and off records both are zero. -/
theorem mixedCharge_eq_rawCharge_of_centering
    (q : ℕ) (a U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℕ → ℝ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n) (hU : ∀ n, 0 < U n)
    (hstate : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) = (U n : ℤ) - V n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n) :
    mixedCharge U (lcmOverlap q a) B f =
      rawCharge U (lcmOverlap q a) B f := by
  funext n
  classical
  by_cases hr : IsStrictRecord U n
  · have hfresh := (strict_record_is_fresh_of_centering
      q a U V hq ha hU hstate hcenter hr).1
    simp [mixedCharge, rawCharge, hr, hfresh]
  · simp [mixedCharge, rawCharge, hr]

/-- Unbounded centred height makes the paper raw record series divergent for
every nonnegative antitone weight divergent on arithmetic progressions. -/
theorem centred_unbounded_not_summable_raw
    (q : ℕ) (a U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n) (hU : ∀ n, 0 < U n)
    (hstate : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) = (U n : ℤ) - V n)
    (herror : ∀ n, V n = (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * U n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n)
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiv : DivergesOnProgressions f) :
    ¬ Summable (rawCharge U (lcmOverlap q a) B f) := by
  obtain ⟨T, x, P, hP, hx, hcover⟩ := centred_actual_lcm_covering
    q a U V B hq ha hU hstate herror hcenter hunbounded
  have harith : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - (cumulativeDigitLcm q a n : ℤ) := by
    intro n
    have hs := hstate n
    rw [herror n] at hs
    nlinarith
  have hmix : ¬ Summable (mixedCharge U (lcmOverlap q a) B f) := by
    exact not_summable_mixed_of_cover U (lcmOverlap q a)
      (fun n ↦ (a n : ℤ)) (fun _ ↦ (1 : ℤ))
      (fun n ↦ (cumulativeDigitLcm q a n : ℤ))
      T x P B hP hx hunbounded
      (fun n ↦ by simpa only [one_mul] using harith n)
      (fun n _hn _hfresh ↦ hcover n _hn) f hf hpos (hdiv x P (by omega))
  rw [mixedCharge_eq_rawCharge_of_centering q a U V B f hq ha hU hstate hcenter] at hmix
  exact hmix

/-- Exact cumulative-LCM identification for an abstract positive sequence
satisfying `L_{n+1}=lcm(L_n,a_n)`. -/
theorem abstract_lcm_eq_cumulative
    (a L : ℕ → ℕ) (hL : ∀ n, L (n + 1) = Nat.lcm (L n) (a n)) :
    ∀ n, L n = cumulativeDigitLcm (L 0) a n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [cumulativeDigitLcm_succ, ← ih]
      exact hL n

/-- **Arithmetic weighted-record dichotomy (exact printed endpoint).**

Positive integer sequences `a,L,U` and integer errors `V` satisfy the exact
LCM update, centred state update, error identity and lower centring bound.
For every fixed baseline `B` and every finite nonnegative nonincreasing weight
whose improper integral from one is unbounded, bounded height is equivalent
to finiteness of the weighted raw record-excess series.
-/
theorem arithmetic_weighted_record_dichotomy
    (a L U : ℕ → ℕ) (V : ℕ → ℤ)
    (ha : ∀ n, 0 < a n) (hLpos : ∀ n, 0 < L n) (hU : ∀ n, 0 < U n)
    (hL : ∀ n, L (n + 1) = Nat.lcm (L n) (a n))
    (hstate : ∀ n, (Nat.gcd (L n) (a n) : ℤ) * U (n + 1) =
      (U n : ℤ) - V n)
    (herror : ∀ n, V n = (L n : ℤ) - ((a n : ℤ) - 1) * U n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n)
    (B : ℕ) (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ H : ℕ, ∀ n, U n ≤ H) ↔ Summable (paperRecordCharge U V B f) := by
  let q := L 0
  have hq : 0 < q := hLpos 0
  have hLid : ∀ n, L n = cumulativeDigitLcm q a n :=
    abstract_lcm_eq_cumulative a L hL
  have hstate' : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (U n : ℤ) - V n := by
    intro n
    simpa [lcmOverlap, ← hLid n] using hstate n
  have herror' : ∀ n, V n = (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * U n := by
    intro n
    simpa [← hLid n] using herror n
  have hcharge : rawCharge U (lcmOverlap q a) B (natWeight f) =
      paperRecordCharge U V B f :=
    rawCharge_eq_paperRecordCharge U (lcmOverlap q a) V B f hU hstate'
  constructor
  · intro hb
    obtain ⟨N, hN⟩ := eventually_no_records_of_bounded U hb
    have hsraw : Summable (rawCharge U (lcmOverlap q a) B (natWeight f)) := by
      apply summable_of_ne_finset_zero (s := Finset.range N)
      intro n hn
      have hn' : N ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      simp [rawCharge, hN n hn']
    rwa [hcharge] at hsraw
  · intro hs
    have hsraw : Summable (rawCharge U (lcmOverlap q a) B (natWeight f)) := by
      rwa [hcharge]
    by_contra hb
    have hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n := by
      intro H
      by_contra hnot
      apply hb
      refine ⟨H, ?_⟩
      intro n
      have hh : ¬ H ≤ U n := fun h ↦ hnot ⟨n, h⟩
      omega
    exact centred_unbounded_not_summable_raw q a U V B hq ha hU hstate' herror'
      hcenter hunbounded (natWeight f) (natWeight_antitone f hf)
      (natWeight_nonneg f hpos) (natWeight_divergesOnProgressions f hf hpos hdiv)
      hsraw

end ErdosProblems.Erdos243.PaperCompleteR11
