import Mathlib

/-!
# Relocated binary-encoding proof

Proof-bearing source slice from BoundedPerturbationCountermodel.lean,
pinned d4fed71423840f70f10edf27b9ad27c22fc4f49a. The binary construction is
not redone: its proof is reused in a fresh namespace with a Mathlib-only
import. Source relocation requires a fresh Lean check; UNRUN here.
-/
noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.BinarySource

def binaryDigit (D : ℝ) (n : ℕ) : ℤ :=
  ⌊(2 : ℝ) ^ (n + 1) * D⌋ - 2 * ⌊(2 : ℝ) ^ n * D⌋

theorem binaryDigit_nonneg (D : ℝ) (n : ℕ) : 0 ≤ binaryDigit D n := by
  unfold binaryDigit
  have h : (2 : ℤ) * ⌊(2 : ℝ) ^ n * D⌋ ≤ ⌊(2 : ℝ) ^ (n + 1) * D⌋ := by
    rw [Int.le_floor]
    push_cast
    have e : (2 : ℝ) ^ (n + 1) * D = 2 * ((2 : ℝ) ^ n * D) := by ring
    rw [e]
    linarith [Int.floor_le ((2 : ℝ) ^ n * D)]
  omega

theorem binaryDigit_le_one (D : ℝ) (n : ℕ) : binaryDigit D n ≤ 1 := by
  unfold binaryDigit
  have h : ⌊(2 : ℝ) ^ (n + 1) * D⌋ < 2 * ⌊(2 : ℝ) ^ n * D⌋ + 2 := by
    rw [Int.floor_lt]
    push_cast
    have e : (2 : ℝ) ^ (n + 1) * D = 2 * ((2 : ℝ) ^ n * D) := by ring
    rw [e]
    linarith [Int.lt_floor_add_one ((2 : ℝ) ^ n * D)]
  omega

theorem sum_binaryDigit_div (D : ℝ) (N : ℕ) :
    ∑ n ∈ range N, (binaryDigit D n : ℝ) / 2 ^ (n + 1) =
      (⌊(2 : ℝ) ^ N * D⌋ : ℝ) / 2 ^ N - (⌊D⌋ : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    unfold binaryDigit
    push_cast
    field_simp
    ring

theorem tendsto_floor_pow_mul_div (D : ℝ) :
    Tendsto (fun N : ℕ => (⌊(2 : ℝ) ^ N * D⌋ : ℝ) / 2 ^ N) atTop (𝓝 D) := by
  have hlow : ∀ N : ℕ, D - 1 / 2 ^ N ≤ (⌊(2 : ℝ) ^ N * D⌋ : ℝ) / 2 ^ N := by
    intro N
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    rw [le_div_iff₀ h2]
    have e : (D - 1 / 2 ^ N) * 2 ^ N = 2 ^ N * D - 1 := by
      rw [sub_mul, one_div, inv_mul_cancel₀ h2.ne']
      ring
    rw [e]
    linarith [Int.lt_floor_add_one ((2 : ℝ) ^ N * D)]
  have hup : ∀ N : ℕ, (⌊(2 : ℝ) ^ N * D⌋ : ℝ) / 2 ^ N ≤ D := by
    intro N
    have h2 : (0 : ℝ) < 2 ^ N := by positivity
    rw [div_le_iff₀ h2]
    have e : D * 2 ^ N = 2 ^ N * D := by ring
    rw [e]
    exact Int.floor_le ((2 : ℝ) ^ N * D)
  have h0 : Tendsto (fun N : ℕ => ((1 : ℝ) / 2) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / 2 ^ N) atTop (𝓝 0) := by
    simpa [one_div_pow] using h0
  have hlim : Tendsto (fun N : ℕ => D - 1 / (2 : ℝ) ^ N) atTop (𝓝 D) := by
    simpa using tendsto_const_nhds.sub h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup

theorem hasSum_binaryDigit (D : ℝ) (h0 : 0 ≤ D) (h1 : D < 1) :
    HasSum (fun n : ℕ => (binaryDigit D n : ℝ) / 2 ^ (n + 1)) D := by
  have hnn : ∀ n : ℕ, 0 ≤ (binaryDigit D n : ℝ) / 2 ^ (n + 1) := fun n =>
    div_nonneg (by exact_mod_cast binaryDigit_nonneg D n) (by positivity)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hfl : ⌊D⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  simp_rw [sum_binaryDigit_div, hfl]
  simpa using tendsto_floor_pow_mul_div D

def rationalisingPerturbationDigits (S r : ℝ) (M : ℕ) (n : ℕ) : ℕ :=
  (binaryDigit ((r - S) / M) n).toNat

theorem exists_bounded_perturbation_digits {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S) (M : ℕ) (hM : 0 < M)
    (r : ℝ) (hr₁ : S < r) (K : ℕ) (hK : r < S + M / 2 ^ K) :
    (∀ n, rationalisingPerturbationDigits S r M n ≤ 1) ∧
      (∀ n < K, rationalisingPerturbationDigits S r M n = 0) ∧
      HasSum (fun n =>
        ((g n + M * rationalisingPerturbationDigits S r M n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have hrs : (r - S) * 2 ^ K < M := by
    have : r - S < M / 2 ^ K := by linarith
    exact (lt_div_iff₀ h2K).mp this
  have hr₂ : r < S + M := by
    have hK1 : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
    nlinarith
  set D : ℝ := (r - S) / M with hD
  have hD0 : 0 ≤ D := div_nonneg (by linarith) hMpos.le
  have hD1 : D < 1 := by rw [hD, div_lt_one hMpos]; linarith
  have hfloor : ∀ m, m ≤ K → ⌊(2 : ℝ) ^ m * D⌋ = 0 := by
    intro m hm
    rw [Int.floor_eq_zero_iff]
    refine ⟨mul_nonneg (by positivity) hD0, ?_⟩
    have h2m : (2 : ℝ) ^ m ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hm
    have hlt : (2 : ℝ) ^ K * D < 1 := by
      rw [hD, mul_div_assoc', div_lt_one hMpos]
      linarith
    calc
      (2 : ℝ) ^ m * D ≤ 2 ^ K * D := mul_le_mul_of_nonneg_right h2m hD0
      _ < 1 := hlt
  refine ⟨?_, ?_, ?_⟩
  · intro n
    unfold rationalisingPerturbationDigits
    have := binaryDigit_le_one ((r - S) / M) n
    have := binaryDigit_nonneg ((r - S) / M) n
    omega
  · intro n hn
    unfold rationalisingPerturbationDigits
    have heq : binaryDigit ((r - S) / M) n = binaryDigit D n := by rw [hD]
    rw [heq]
    simp [binaryDigit, hfloor (n + 1) (by omega), hfloor n (by omega)]
  · have hcast : ∀ n, (((binaryDigit D n).toNat : ℕ) : ℝ) = (binaryDigit D n : ℝ) := by
      intro n
      have := binaryDigit_nonneg D n
      exact_mod_cast Int.toNat_of_nonneg this
    have h1 := hasSum_binaryDigit D hD0 hD1
    convert hS.add (h1.mul_left (M : ℝ)) using 1
    · funext n
      unfold rationalisingPerturbationDigits
      push_cast
      rw [hD, hcast]
      ring
    · have hMD : (M : ℝ) * D = r - S := by
        rw [hD]
        field_simp
      linarith

theorem exists_bounded_perturbation {g : ℕ → ℕ} {S : ℝ}
    (hS : HasSum (fun n => (g n : ℝ) / 2 ^ (n + 1)) S) (M : ℕ) (hM : 0 < M)
    (r : ℝ) (hr₁ : S < r) (K : ℕ) (hK : r < S + M / 2 ^ K) :
    ∃ δ : ℕ → ℕ, (∀ n, δ n ≤ 1) ∧ (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((g n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) r :=
  ⟨rationalisingPerturbationDigits S r M,
    exists_bounded_perturbation_digits hS M hM r hr₁ K hK⟩

#print axioms exists_bounded_perturbation
end ErdosProblems.Erdos251.PaperR11.BinarySource
