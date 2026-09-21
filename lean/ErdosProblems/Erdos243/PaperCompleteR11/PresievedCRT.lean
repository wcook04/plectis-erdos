import ErdosProblems.Erdos243.PaperCompleteR11.RecordDivisibility
import Mathlib.Data.Nat.Totient

/-!
# Exact finite pre-sieving and the primitive record fence


The modulus W is part of the CRT construction, not merely mentioned in
an offset-counting hypothesis.  Thus x is a multiple of W, and only the
phi(W)/W proportion of offsets coprime to W need individual old moduli.
The exact count, its asymptotic proportion, the bounded CRT phase and the
primitive first-crossing contradiction are all supplied here.  Selection
of the canonical moduli and the final log-log limit remain separate.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter
open scoped BigOperators Topology

/-- The offsets not already excluded by the old primitive denominator W. -/
def presievedOffsets (W B : ℕ) : Finset ℕ :=
  (Finset.range B).filter (fun r ↦ Nat.Coprime W r)

/-- One complete residue block contains exactly Euler's totient. -/
theorem presievedOffsets_card_mul (W k : ℕ) :
    (presievedOffsets W (k * W)).card = k * Nat.totient W := by
  classical
  induction k with
  | zero => simp [presievedOffsets]
  | succ k ih =>
      have hunion : presievedOffsets W ((k + 1) * W) =
          presievedOffsets W (k * W) ∪
            ((Finset.Ico (k * W) (k * W + W)).filter (fun r ↦ Nat.Coprime W r)) := by
        rw [Nat.add_mul, Nat.one_mul]
        ext r
        simp only [presievedOffsets, Finset.mem_filter, Finset.mem_range,
          Finset.mem_union, Finset.mem_Ico]
        omega
      have hdisj : Disjoint (presievedOffsets W (k * W))
          ((Finset.Ico (k * W) (k * W + W)).filter (fun r ↦ Nat.Coprime W r)) := by
        apply Finset.disjoint_left.mpr
        intro r hr hs
        have hlt := (Finset.mem_filter.mp hr).1
        have hge := (Finset.mem_Ico.mp (Finset.mem_filter.mp hs).1).1
        have hlt' := Finset.mem_range.mp hlt
        omega
      rw [hunion, Finset.card_union_of_disjoint hdisj, ih,
        Nat.filter_coprime_Ico_eq_totient]
      ring

/-- Two exact integer bounds, including the empty prefix. -/
theorem presievedOffsets_card_bounds (W B : ℕ) (hW : 0 < W) :
    (B / W) * Nat.totient W ≤ (presievedOffsets W B).card ∧
      (presievedOffsets W B).card ≤ (B / W + 1) * Nat.totient W := by
  have hmod := Nat.mod_add_div B W
  have hmodlt := Nat.mod_lt B hW
  have hlow : (B / W) * W ≤ B := Nat.div_mul_le_self B W
  have hhigh : B ≤ (B / W + 1) * W := by nlinarith
  have hmono : ∀ b c : ℕ, b ≤ c → (presievedOffsets W b).card ≤
      (presievedOffsets W c).card := by
    intro b c hbc
    apply Finset.card_le_card
    intro r hr
    simp only [presievedOffsets, Finset.mem_filter, Finset.mem_range] at hr ⊢
    exact ⟨hr.1.trans_le hbc, hr.2⟩
  constructor
  · simpa only [presievedOffsets_card_mul] using hmono ((B / W) * W) B hlow
  · simpa only [presievedOffsets_card_mul] using hmono B ((B / W + 1) * W) hhigh

/-- An explicit uniform real error bound for the coprime offset count. -/
theorem presievedOffsets_card_error (W B : ℕ) (hW : 0 < W) :
    |((presievedOffsets W B).card : ℝ) -
      (Nat.totient W : ℝ) / (W : ℝ) * (B : ℝ)| ≤ (Nat.totient W : ℝ) := by
  obtain ⟨hlo, hhi⟩ := presievedOffsets_card_bounds W B hW
  have hmod := Nat.mod_add_div B W
  have hmodlt := Nat.mod_lt B hW
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hphi : (0 : ℝ) ≤ (Nat.totient W : ℝ) := by positivity
  have hloR : ((B / W : ℕ) : ℝ) * (Nat.totient W : ℝ) ≤
      ((presievedOffsets W B).card : ℝ) := by exact_mod_cast hlo
  have hhiR : ((presievedOffsets W B).card : ℝ) ≤
      (((B / W : ℕ) : ℝ) + 1) * (Nat.totient W : ℝ) := by exact_mod_cast hhi
  have hBlow : ((B / W : ℕ) : ℝ) * (W : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast (Nat.div_mul_le_self B W)
  have hBhigh : (B : ℝ) ≤ (((B / W : ℕ) : ℝ) + 1) * (W : ℝ) := by
    exact_mod_cast (show B ≤ (B / W + 1) * W by nlinarith)
  have hratioLo : ((B / W : ℕ) : ℝ) ≤ (B : ℝ) / (W : ℝ) :=
    (le_div_iff₀ hWpos).2 hBlow
  have hratioHi : (B : ℝ) / (W : ℝ) ≤ ((B / W : ℕ) : ℝ) + 1 :=
    (div_le_iff₀ hWpos).2 hBhigh
  have hmulLo := mul_le_mul_of_nonneg_left hratioLo hphi
  have hmulHi := mul_le_mul_of_nonneg_left hratioHi hphi
  have hid : (Nat.totient W : ℝ) / (W : ℝ) * (B : ℝ) =
      (Nat.totient W : ℝ) * ((B : ℝ) / (W : ℝ)) := by ring
  rw [hid, abs_le]
  constructor <;> nlinarith

/-- The precise asymptotic proportion used in the strict inclusive constant. -/
theorem presievedOffsets_density (W : ℕ) (hW : 0 < W) :
    Tendsto (fun B : ℕ ↦ ((presievedOffsets W B).card : ℝ) / (B : ℝ))
      atTop (𝓝 ((Nat.totient W : ℝ) / (W : ℝ))) := by
  apply Metric.tendsto_atTop.2
  intro δ hδ
  obtain ⟨M, hM⟩ := exists_nat_gt (max (1 : ℝ) ((Nat.totient W : ℝ) / δ))
  refine ⟨M, fun B hMB ↦ ?_⟩
  have hMBR : (M : ℝ) ≤ (B : ℝ) := by exact_mod_cast hMB
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have hh := (le_max_left (1 : ℝ) ((Nat.totient W : ℝ) / δ)).trans_lt hM
    linarith
  have hsmall : (Nat.totient W : ℝ) / (B : ℝ) < δ := by
    apply (div_lt_iff₀ hBpos).2
    have hh : (Nat.totient W : ℝ) / δ < (B : ℝ) :=
      ((le_max_right (1 : ℝ) ((Nat.totient W : ℝ) / δ)).trans_lt hM).trans_le hMBR
    have hh' := (div_lt_iff₀ hδ).1 hh
    nlinarith
  have herr := presievedOffsets_card_error W B hW
  have hW0 : (W : ℝ) ≠ 0 := by exact_mod_cast hW.ne'
  have hid : ((presievedOffsets W B).card : ℝ) / (B : ℝ) -
      (Nat.totient W : ℝ) / (W : ℝ) =
      (((presievedOffsets W B).card : ℝ) -
        (Nat.totient W : ℝ) / (W : ℝ) * (B : ℝ)) / (B : ℝ) := by
    field_simp [hBpos.ne', hW0]
    <;> ring
  rw [Real.dist_eq, hid, abs_div, abs_of_pos hBpos]
  exact (div_le_div_of_nonneg_right herr hBpos.le).trans_lt hsmall

/-- The totient improvement is strictly greater than one whenever W > 1. -/
theorem presieved_totient_ratio_gt_one (W : ℕ) (hW : 1 < W) :
    (1 : ℝ) < (W : ℝ) / (Nat.totient W : ℝ) := by
  have hphi : (0 : ℝ) < (Nat.totient W : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < W))
  apply (lt_div_iff₀ hphi).2
  simpa only [one_mul] using (show (Nat.totient W : ℝ) < (W : ℝ) by
    exact_mod_cast Nat.totient_lt W hW)

/-- Bounded CRT with an additional old modulus W and arbitrary assigned
(non-consecutive) offsets.  No existence of a residue class is assumed. -/
theorem exists_presieved_crt_phase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ℕ) (hW : 0 < W) (m offset : ι → ℕ)
    (hm : ∀ i, 0 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (hWm : ∀ i, Nat.Coprime W (m i)) :
    ∃ x : ℕ, W * (∏ i, m i) ≤ x ∧ x < 2 * (W * (∏ i, m i)) ∧
      W ∣ x ∧ ∀ i, m i ∣ x + offset i := by
  classical
  let residue : ι → ℕ := fun i ↦ m i - offset i % m i
  have hm0 : ∀ i ∈ (Finset.univ : Finset ι), m i ≠ 0 := fun i _ ↦ (hm i).ne'
  have hpairSet : Set.Pairwise (↑(Finset.univ : Finset ι) : Set ι)
      (fun i j ↦ Nat.Coprime (m i) (m j)) := by
    intro i _ j _ hij
    exact hpair i j hij
  let y₀ := Nat.chineseRemainderOfFinset residue m Finset.univ hm0 hpairSet
  let P₀ : ℕ := ∏ i, m i
  have hWP₀ : Nat.Coprime W P₀ := Nat.coprime_fintype_prod_right_iff.mpr hWm
  let y := Nat.chineseRemainder hWP₀ 0 (y₀ : ℕ)
  let P : ℕ := W * P₀
  have hPpos : 0 < P := mul_pos hW (Finset.prod_pos (fun i _ ↦ hm i))
  let x : ℕ := (y : ℕ) % P + P
  have hmodLt := Nat.mod_lt (y : ℕ) hPpos
  have hxmod {d : ℕ} (hd : d ∣ P) : x ≡ (y : ℕ) [MOD d] := by
    have h₁ := (Nat.mod_modEq (y : ℕ) P).of_dvd hd
    have h₂ : P ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hd
    simpa only [add_zero] using h₁.add h₂
  refine ⟨x, by dsimp [x, P, P₀] at *; omega,
    by dsimp [x, P, P₀] at *; omega, ?_, fun i ↦ ?_⟩
  · exact Nat.modEq_zero_iff_dvd.mp
      ((hxmod (dvd_mul_right W P₀)).trans y.property.1)
  · have hmP₀ : m i ∣ P₀ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    have hmP : m i ∣ P := hmP₀.trans (dvd_mul_left P₀ W)
    have hyi : (y : ℕ) ≡ residue i [MOD m i] :=
      (y.property.2.of_dvd hmP₀).trans (y₀.property i (Finset.mem_univ i))
    have hres : m i ∣ residue i + offset i := by
      let r := offset i % m i
      let q := offset i / m i
      have hrem : r < m i := by simpa only [r] using Nat.mod_lt (offset i) (hm i)
      have hdiv : r + m i * q = offset i := by
        simpa only [r, q] using Nat.mod_add_div (offset i) (m i)
      refine ⟨q + 1, ?_⟩
      change m i - r + offset i = m i * (q + 1)
      conv_lhs => rhs; rw [← hdiv]
      rw [← Nat.add_assoc, Nat.sub_add_cancel hrem.le]
      simp [Nat.mul_succ, Nat.add_comm]
    have hcong : x + offset i ≡ residue i + offset i [MOD m i] :=
      ((hxmod hmP).trans hyi).add_right (offset i)
    exact Nat.modEq_zero_iff_dvd.mp
      (hcong.trans (Nat.modEq_zero_iff_dvd.mpr hres))

/-- When x is a multiple of W, an admissible number in its block has a
coprime offset and is therefore covered by one of the assigned moduli. -/
theorem presieved_phase_covers_admissible
    (W B x : ℕ) (m : {r // r ∈ presievedOffsets W B} → ℕ)
    (hWx : W ∣ x)
    (hphase : ∀ i, m i ∣ x + i.val)
    (z : ℕ) (hxz : x ≤ z) (hzb : z < x + B) (hcop : Nat.Coprime W z) :
    ∃ i : {r // r ∈ presievedOffsets W B}, m i ∣ z := by
  let r := z - x
  have hxr : x + r = z := Nat.add_sub_of_le hxz
  have hrB : r < B := by dsimp [r]; omega
  have hcopr : Nat.Coprime W r := by
    have hdW := Nat.gcd_dvd_left W r
    have hdr := Nat.gcd_dvd_right W r
    have hdz : Nat.gcd W r ∣ z := by
      rw [← hxr]
      exact dvd_add (hdW.trans hWx) hdr
    have hd1 : Nat.gcd W r ∣ 1 := by
      simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hdW hdz
    exact Nat.dvd_one.mp hd1
  let i : {r // r ∈ presievedOffsets W B} :=
    ⟨r, by simp only [presievedOffsets, Finset.mem_filter, Finset.mem_range]; exact ⟨hrB, hcopr⟩⟩
  refine ⟨i, ?_⟩
  simpa only [i, hxr] using hphase i

/-- A primitive orbit cannot first cross a pre-sieved covered record block
with record increments at most B.  Arbitrarily deep drawdowns are allowed. -/
theorem presieved_primitive_record_fence
    (U D : ℕ → ℕ) (W B T x : ℕ)
    (m : {r // r ∈ presievedOffsets W B} → ℕ)
    (hm : ∀ i, 1 < m i)
    (hprimitive : ∀ n, T ≤ n → Nat.Coprime (U n) (D n))
    (hWold : ∀ n, T ≤ n → W ∣ D n)
    (hmOld : ∀ i n, T ≤ n → m i ∣ D n)
    (hWx : W ∣ x) (hphase : ∀ i, m i ∣ x + i.val)
    (hprefix : runningMax U T < x)
    (hcap : ∀ n, T ≤ n → runningMax U n < x + B →
      runningMax U n < U (n + 1) → U (n + 1) - runningMax U n ≤ B) :
    ∀ n, U n < x + B := by
  intro k
  by_contra hk
  have hzero : U 0 < x + B := by
    have hh := le_runningMax U (Nat.zero_le T)
    omega
  obtain ⟨n, hn, _⟩ := LcmRecordCrossing.exists_unique_firstCrossing U
    (x + B) k hzero ⟨k, le_rfl, by omega⟩
  have hTn : T ≤ n := by
    by_contra hbad
    have hh := le_runningMax U (show n + 1 ≤ T by omega)
    have hh' := hn.2.2
    omega
  have hRlt : runningMax U n < x + B := runningMax_lt U hn.2.1
  have hRnew : runningMax U n < U (n + 1) := hRlt.trans_le hn.2.2
  have hgap := hcap n hTn hRlt hRnew
  have hnext_le : U (n + 1) ≤ runningMax U n + B := by
    calc
      U (n + 1) = runningMax U n + (U (n + 1) - runningMax U n) :=
        (Nat.add_sub_of_le hRnew.le).symm
      _ ≤ runningMax U n + B := Nat.add_le_add_left hgap _
  have hxR : x ≤ runningMax U n :=
    Nat.le_of_add_le_add_right (hn.2.2.trans hnext_le)
  obtain ⟨j, hjn, hjR⟩ := runningMax_attained U n
  have hTj : T ≤ j := by
    by_contra hbad
    have hh := le_runningMax U (show j ≤ T by omega)
    omega
  have hcop : Nat.Coprime W (U j) :=
    ((hprimitive j hTj).of_dvd_right (hWold j hTj)).symm
  obtain ⟨i, hi⟩ := presieved_phase_covers_admissible W B x m hWx hphase
    (U j) (by omega) (by omega) hcop
  have hd : m i ∣ 1 := by
    simpa only [(hprimitive j hTj).gcd_eq_one] using Nat.dvd_gcd hi (hmOld i j hTj)
  have h1 := Nat.dvd_one.mp hd
  have hbig := hm i
  omega

/-- The primitive fence composed with the actual pre-sieved CRT supplier.
Its remaining size hypothesis is an explicit finite product comparison. -/
theorem presieved_primitive_record_fence_from_moduli
    (U D : ℕ → ℕ) (W B T : ℕ) (hW : 0 < W)
    (m : {r // r ∈ presievedOffsets W B} → ℕ)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (hWm : ∀ i, Nat.Coprime W (m i))
    (hprimitive : ∀ n, T ≤ n → Nat.Coprime (U n) (D n))
    (hWold : ∀ n, T ≤ n → W ∣ D n)
    (hmOld : ∀ i n, T ≤ n → m i ∣ D n)
    (hsize : runningMax U T < W * ∏ i, m i) :
    ∃ x : ℕ, W * (∏ i, m i) ≤ x ∧ x < 2 * (W * (∏ i, m i)) ∧
      ((∀ n, T ≤ n → runningMax U n < x + B → runningMax U n < U (n + 1) →
        U (n + 1) - runningMax U n ≤ B) → ∀ n, U n < x + B) := by
  classical
  obtain ⟨x, hxlo, hxhi, hWx, hphase⟩ := exists_presieved_crt_phase W hW m
    (fun i ↦ i.val) (fun i ↦ by have hh := hm i; omega) hpair hWm
  refine ⟨x, hxlo, hxhi, ?_⟩
  intro hcap
  exact presieved_primitive_record_fence U D W B T x m hm hprimitive hWold hmOld
    hWx hphase (hsize.trans_le hxlo) hcap

end ErdosProblems.Erdos243.PaperCompleteR11
