import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
Paper-form transcription of the long Erdős #257 `lem` at
`paper/reasoning-parts/erdos257/a257_front.tex:7945`
("Divisor-residue form of the short-window phase", `lem:odometer`), together with
the definition `defn:theta` (line 7850) that it is stated about.

Nothing in the tree defined `Θ_L(M)`, `i_d(M)` or `m_d`, so all three are defined
here by direct transcription:

* `Theta L M = ∑_{i=1}^{L} (τ(M+i) − 1) 2^{-i}`  (`defn:theta`);
* `iLeast d M = d − M % d`, the least `i ≥ 1` with `d ∣ M + i`;
* `mCount d M L = #{1 ≤ i ≤ L : d ∣ M + i}`.

The two displayed identities of the lemma are `theta_eq_divisorResidueSum`
(residue double sum) and `theta_eq_geometricForm` (geometric collapse), each in a
finite-cutoff form valid for every `D ≥ M + L` and in the literal `∑_{d ≥ 2}`
form `theta_eq_tsum_divisorResidue` / `theta_eq_tsum_geometricForm`.  The side
conditions of the `where` clause are `iLeast_mem_Icc`, `dvd_add_iLeast`,
`not_dvd_of_lt_iLeast`, `iLeast_congr`, and the "terms with `i_d(M) > L` are
empty" convention is `geometric_term_eq_zero_of_lt_iLeast`.

DEFECT (closing sentence).  The lemma ends "In particular `Θ_L(M)` is a function
of the residues of `M` modulo every `d ≤ M+L`, and nothing else."  That sentence
has no true, non-degenerate transcription, because the cutoff `M+L` itself moves
with `M`:

* comparing two arguments through one argument's cutoff is FALSE.
  `residue_cutoff_reading_fails`: `1 ≡ 3 (mod d)` for every `d ≤ 1 + 1 = M + L`,
  yet `Θ_1(1) = 1/2` and `Θ_1(3) = 1`;
* comparing them through a cutoff that dominates both is VACUOUS.
  `eq_of_residues_agree`: agreement of `M % d` for all `2 ≤ d ≤ D` with
  `M, M' ≤ D` already forces `M = M'`, so the determination statement is empty.

The corrected statement, which is the content the surrounding text actually uses,
fixes the cutoff first: `theta_eq_Psi` says `Θ_L(M) = Ψ_{L,D}(M)` for every
`D ≥ M+L`, and `Psi_eq_of_residues_eq` says `Ψ_{L,D}` depends on its argument
only through the residues modulo `2 ≤ d ≤ D` (hence `Psi_add_of_forall_dvd`:
`Ψ_{L,D}` is periodic with any period divisible by each such `d`, in particular
`Q_D = lcm(1,…,D)`).  Both are proved below.

The lemma's trailing `\ev{Cert}` sentence ("verified exactly as rationals at
`(M,L) ∈ {1000,10001,123456} × {12,20}`") is an empirical probe report and is not
transcribed.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21
namespace ShortWindowDivisorPhase

/-! ### Definitions transcribed from the paper -/

/-- Definition `defn:theta` (line 7850): the short-window divisor phase
`Θ_L(M) = ∑_{i=1}^{L} (τ(M+i) − 1) 2^{-i}`, where `τ` is the number-of-divisors
function.  For `M ≥ 1` and `1 ≤ i` the truncated subtraction is the honest
`τ(M+i) − 1` because `M + i ≥ 1`; see `card_divisors_sub_one` for the paper's own
gloss `τ(n) − 1 = #{d ≥ 2 : d ∣ n}`. -/
def Theta (L M : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 L, (((M + i).divisors.card - 1 : ℕ) : ℚ) * (1 / 2 : ℚ) ^ i

/-- `i_d(M)`: the least `i ≥ 1` with `d ∣ M + i`.  Equal to `d − (M mod d)`, with
value `d` when the remainder is zero, and manifestly a function of `M mod d`. -/
def iLeast (d M : ℕ) : ℕ := d - M % d

/-- `m_d = #{1 ≤ i ≤ L : d ∣ M + i}`. -/
def mCount (d M L : ℕ) : ℕ := ((Finset.Icc 1 L).filter (fun i => d ∣ M + i)).card

/-- `Ψ_{L,D}(x) = ∑_{d=2}^{D} ∑_{i=1}^{L} 2^{-i} 1_{d ∣ x+i}`, the finite-cutoff
residue form (paper line 7966). -/
def Psi (L D x : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 2 D, ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ x + i), (1 / 2 : ℚ) ^ i

/-! ### Small interval facts -/

private lemma Icc_one_zero : Finset.Icc 1 0 = (∅ : Finset ℕ) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_Icc] at hi
    omega
  · intro hi
    exact absurd hi (Finset.notMem_empty i)

private lemma Icc_one_succ (L : ℕ) :
    Finset.Icc 1 (L + 1) = insert (L + 1) (Finset.Icc 1 L) := by
  ext i
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

private lemma notMem_Icc_one (L : ℕ) : (L + 1) ∉ Finset.Icc 1 L := by
  simp only [Finset.mem_Icc]
  omega

private lemma half_pow_le_one (e : ℕ) : (1 / 2 : ℚ) ^ e ≤ 1 := by
  induction e with
  | zero => norm_num
  | succ n ih =>
      have hp : (0 : ℚ) < (1 / 2 : ℚ) ^ n := pow_pos (by norm_num) n
      rw [pow_succ]
      linarith

private lemma one_sub_half_pow_pos {d : ℕ} (hd : 1 ≤ d) :
    (0 : ℚ) < 1 - (1 / 2 : ℚ) ^ d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have h := half_pow_le_one e
  have hp : (0 : ℚ) < (1 / 2 : ℚ) ^ e := pow_pos (by norm_num) e
  rw [pow_succ]
  linarith

/-! ### The congruence condition -/

/-- The paper's inner condition `i ≡ −M (mod d)` is exactly `d ∣ M + i`. -/
theorem residue_condition_iff (d M i : ℕ) :
    ((i : ℤ) ≡ -(M : ℤ) [ZMOD (d : ℤ)]) ↔ d ∣ M + i := by
  rw [Int.modEq_iff_dvd]
  have hrw : -(M : ℤ) - (i : ℤ) = -((M : ℤ) + (i : ℤ)) := by ring
  rw [hrw]
  constructor
  · intro h
    have h2 : (d : ℤ) ∣ ((M : ℤ) + (i : ℤ)) := (dvd_neg).mp h
    exact_mod_cast h2
  · intro h
    have h2 : (d : ℤ) ∣ ((M : ℤ) + (i : ℤ)) := by exact_mod_cast h
    exact (dvd_neg).mpr h2

/-! ### `i_d(M)`: the `where` clause of the lemma -/

/-- `i_d(M) ∈ [1, d]`. -/
theorem iLeast_mem_Icc (d M : ℕ) (hd : 1 ≤ d) : 1 ≤ iLeast d M ∧ iLeast d M ≤ d := by
  have h := Nat.mod_lt M (show 0 < d from hd)
  simp only [iLeast]
  omega

/-- `d ∣ M + i_d(M)`. -/
theorem dvd_add_iLeast (d M : ℕ) (hd : 1 ≤ d) : d ∣ M + iLeast d M := by
  refine ⟨M / d + 1, ?_⟩
  have h := Nat.div_add_mod M d
  have h2 := Nat.mod_lt M (show 0 < d from hd)
  have hexp : d * (M / d + 1) = d * (M / d) + d := by ring
  simp only [iLeast]
  omega

/-- `i_d(M)` is the *least* such `i ≥ 1`. -/
theorem not_dvd_of_lt_iLeast (d M i : ℕ) (hd : 1 ≤ d) (hi : 1 ≤ i)
    (hlt : i < iLeast d M) : ¬ d ∣ M + i := by
  intro hdvd
  have h1 := dvd_add_iLeast d M hd
  have h2 : d ∣ (M + iLeast d M) - (M + i) := Nat.dvd_sub h1 hdvd
  have h3 : (M + iLeast d M) - (M + i) = iLeast d M - i := by omega
  rw [h3] at h2
  have h4 : 0 < iLeast d M - i := by omega
  have h5 : d ≤ iLeast d M - i := Nat.le_of_dvd h4 h2
  have h6 := (iLeast_mem_Icc d M hd).2
  omega

/-- `i_d(M)` depends only on `M mod d`. -/
theorem iLeast_congr (d M M' : ℕ) (h : M % d = M' % d) : iLeast d M = iLeast d M' := by
  simp only [iLeast, h]

/-! ### `m_d` -/

theorem mCount_zero (d M : ℕ) : mCount d M 0 = 0 := by
  simp [mCount]

private lemma dvd_shift (d M k : ℕ) : d ∣ M + k ↔ d ∣ (M % d + k) := by
  have hsplit : M + k = d * (M / d) + (M % d + k) := by
    have h := Nat.div_add_mod M d
    omega
  have h3 : d ∣ d * (M / d) := ⟨M / d, rfl⟩
  constructor
  · intro h
    rw [hsplit] at h
    have h4 := Nat.dvd_sub h h3
    simpa using h4
  · intro h
    have h5 : d ∣ d * (M / d) + (M % d + k) := dvd_add h3 h
    rw [← hsplit] at h5
    exact h5

theorem mCount_succ_of_dvd (d M L : ℕ) (hdvd : d ∣ M + (L + 1)) :
    mCount d M (L + 1) = mCount d M L + 1 := by
  have hnmf : (L + 1) ∉ (Finset.Icc 1 L).filter (fun i => d ∣ M + i) := fun h =>
    notMem_Icc_one L (Finset.mem_of_mem_filter _ h)
  simp only [mCount, Icc_one_succ, Finset.filter_insert, if_pos hdvd]
  exact Finset.card_insert_of_notMem hnmf

theorem mCount_succ_of_not_dvd (d M L : ℕ) (hdvd : ¬ d ∣ M + (L + 1)) :
    mCount d M (L + 1) = mCount d M L := by
  simp only [mCount, Icc_one_succ, Finset.filter_insert, if_neg hdvd]

/-- Closed form for the count: `m_d = ⌊(L + M mod d)/d⌋`; in particular `m_d`
depends on `M` only through `M mod d`. -/
theorem mCount_eq_div (d M L : ℕ) (hd : 1 ≤ d) : mCount d M L = (L + M % d) / d := by
  have hd0 : 0 < d := hd
  induction L with
  | zero =>
      rw [mCount_zero, Nat.zero_add]
      exact (Nat.div_eq_of_lt (Nat.mod_lt M hd0)).symm
  | succ L ih =>
      have hiff : d ∣ M + (L + 1) ↔ d ∣ (L + M % d + 1) := by
        rw [dvd_shift d M (L + 1)]
        have hc : M % d + (L + 1) = L + M % d + 1 := by omega
        rw [hc]
      have hcomm : L + 1 + M % d = L + M % d + 1 := by omega
      by_cases hdvd : d ∣ M + (L + 1)
      · rw [mCount_succ_of_dvd d M L hdvd, ih, hcomm, Nat.succ_div,
            if_pos (hiff.mp hdvd)]
      · rw [mCount_succ_of_not_dvd d M L hdvd, ih, hcomm, Nat.succ_div,
            if_neg (fun h => hdvd (hiff.mpr h)), Nat.add_zero]

theorem mCount_congr (d M M' L : ℕ) (hd : 1 ≤ d) (h : M % d = M' % d) :
    mCount d M L = mCount d M' L := by
  rw [mCount_eq_div d M L hd, mCount_eq_div d M' L hd, h]

/-- The exponent identity behind the geometric collapse: when `d ∣ M + (L+1)`,
the offset `L+1` is exactly `i_d(M) + d·m_d(L)`. -/
theorem exponent_identity (d M L : ℕ) (hd : 1 ≤ d) (hdvd : d ∣ M + (L + 1)) :
    iLeast d M + d * mCount d M L = L + 1 := by
  have hd0 : 0 < d := hd
  have hr : M % d < d := Nat.mod_lt M hd0
  have hdm : d ∣ (L + M % d + 1) := by
    have h := (dvd_shift d M (L + 1)).mp hdvd
    have hc : M % d + (L + 1) = L + M % d + 1 := by omega
    rwa [hc] at h
  obtain ⟨s, hs⟩ := hdm
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hs
    omega
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
  have hexpand : d * (u + 1) = d * u + d := by ring
  have hLr : L + M % d = (d - 1) + d * u := by omega
  have hmc : mCount d M L = u := by
    rw [mCount_eq_div d M L hd, hLr, Nat.add_mul_div_left _ _ hd0,
        Nat.div_eq_of_lt (by omega)]
    omega
  rw [hmc]
  simp only [iLeast]
  omega

/-! ### The geometric collapse of one divisor's inner sum -/

/-- The inner sum of the first displayed identity collapses to the geometric
closed form of the second.  `m_d = 0` makes the closed form vanish, which is the
lemma's "terms with `i_d(M) > L` are empty" convention. -/
theorem inner_sum_eq (d M : ℕ) (hd : 1 ≤ d) (L : ℕ) :
    ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ M + i), (1 / 2 : ℚ) ^ i
      = (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
          / (1 - (1 / 2 : ℚ) ^ d) := by
  induction L with
  | zero =>
      rw [mCount_zero]
      simp
  | succ L ih =>
      have hnmf : (L + 1) ∉ (Finset.Icc 1 L).filter (fun i => d ∣ M + i) := fun h =>
        notMem_Icc_one L (Finset.mem_of_mem_filter _ h)
      by_cases hdvd : d ∣ M + (L + 1)
      · rw [Icc_one_succ, Finset.filter_insert, if_pos hdvd, Finset.sum_insert hnmf,
            ih, mCount_succ_of_dvd d M L hdvd]
        have hexp : iLeast d M + d * mCount d M L = L + 1 :=
          exponent_identity d M L hd hdvd
        have hne : (1 : ℚ) - (1 / 2 : ℚ) ^ d ≠ 0 := ne_of_gt (one_sub_half_pow_pos hd)
        have hkey : (1 / 2 : ℚ) ^ (L + 1)
            = (1 / 2 : ℚ) ^ (iLeast d M) * ((1 / 2 : ℚ) ^ d) ^ (mCount d M L) := by
          rw [← pow_mul, ← pow_add, hexp]
        rw [hkey]
        simp only [pow_mul, pow_succ]
        field_simp
        ring
      · rw [Icc_one_succ, Finset.filter_insert, if_neg hdvd,
            mCount_succ_of_not_dvd d M L hdvd]
        exact ih

/-- The "terms with `i_d(M) > L` are empty" convention, as a count. -/
theorem mCount_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d) (h : L < iLeast d M) :
    mCount d M L = 0 := by
  have hempty : (Finset.Icc 1 L).filter (fun i => d ∣ M + i) = ∅ := by
    ext i
    constructor
    · intro hi
      rw [Finset.mem_filter, Finset.mem_Icc] at hi
      obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
      exact absurd hi3 (not_dvd_of_lt_iLeast d M i hd hi1 (by omega))
    · intro hi
      exact absurd hi (Finset.notMem_empty i)
  simp [mCount, hempty]

/-- The "terms with `i_d(M) > L` are empty" convention, as the vanishing of the
geometric summand. -/
theorem geometric_term_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d)
    (h : L < iLeast d M) :
    (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
        / (1 - (1 / 2 : ℚ) ^ d) = 0 := by
  rw [mCount_eq_zero_of_lt_iLeast d M L hd h]
  simp

/-! ### `τ(n) − 1` as the count of divisors `≥ 2` -/

/-- The paper's own gloss of `τ(n) − 1` (line 7856). -/
theorem card_divisors_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card - 1 : ℕ) = (n.divisors.filter (fun d => 2 ≤ d)).card := by
  have hset : n.divisors.filter (fun d => 2 ≤ d) = n.divisors.erase 1 := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, h2⟩
      exact ⟨by omega, hd⟩
    · rintro ⟨hne, hdvd, hn0⟩
      have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with rfl | hp
        · exact absurd (zero_dvd_iff.mp hdvd) (by omega)
        · exact hp
      exact ⟨⟨hdvd, hn0⟩, by omega⟩
  rw [hset, Finset.card_erase_of_mem (Nat.one_mem_divisors.mpr (by omega))]

private lemma card_divisor_window (n D : ℕ) (hn : 2 ≤ n) (hnD : n ≤ D) :
    ((Finset.Icc 2 D).filter (fun d => d ∣ n)).card = n.divisors.card - 1 := by
  have hset : (Finset.Icc 2 D).filter (fun d => d ∣ n) = n.divisors.erase 1 := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h2, hD'⟩, hdvd⟩
      exact ⟨by omega, hdvd, by omega⟩
    · rintro ⟨hne, hdvd, hn0⟩
      have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with rfl | hp
        · exact absurd (zero_dvd_iff.mp hdvd) (by omega)
        · exact hp
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      exact ⟨⟨by omega, by omega⟩, hdvd⟩
  rw [hset, Finset.card_erase_of_mem (Nat.one_mem_divisors.mpr (by omega))]

/-! ### The lemma -/

/-- Core form: `Θ_L(M) = Ψ_{L,D}(M)` for every cutoff `D ≥ M + L`. -/
theorem theta_eq_Psi (M L D : ℕ) (hM : 1 ≤ M) (hD : M + L ≤ D) :
    Theta L M = Psi L D M := by
  have hrhs : Psi L D M
      = ∑ i ∈ Finset.Icc 1 L, ∑ d ∈ Finset.Icc 2 D,
          (if d ∣ M + i then (1 / 2 : ℚ) ^ i else 0) := by
    simp only [Psi]
    have hstep : ∀ d : ℕ,
        (∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ M + i), (1 / 2 : ℚ) ^ i)
          = ∑ i ∈ Finset.Icc 1 L, (if d ∣ M + i then (1 / 2 : ℚ) ^ i else 0) := by
      intro d
      exact Finset.sum_filter _ _
    simp_rw [hstep]
    exact Finset.sum_comm
  rw [hrhs]
  simp only [Theta]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  have h2 : 2 ≤ M + i := by omega
  have hle : M + i ≤ D := by omega
  have hcard : ((M + i).divisors.card - 1 : ℕ)
      = ((Finset.Icc 2 D).filter (fun d => d ∣ M + i)).card :=
    (card_divisor_window (M + i) D h2 hle).symm
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]

/-- First displayed identity of `lem:odometer` (line 7949), in the finite-cutoff
form: for every `D ≥ M + L`,
`Θ_L(M) = ∑_{d=2}^{D} ∑_{1 ≤ i ≤ L, i ≡ −M (mod d)} 2^{-i}`.
The cutoff is harmless: `theta_eq_tsum_divisorResidue` gives the literal
`∑_{d ≥ 2}`. -/
theorem theta_eq_divisorResidueSum (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ M + i), (1 / 2 : ℚ) ^ i :=
  theta_eq_Psi M L D hM hD

/-- Second displayed identity of `lem:odometer` (line 7949), in the finite-cutoff
form: for every `D ≥ M + L`,
`Θ_L(M) = ∑_{d=2}^{D} 2^{-i_d(M)} (1 − 2^{-d m_d}) / (1 − 2^{-d})`. -/
theorem theta_eq_geometricForm (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
            / (1 - (1 / 2 : ℚ) ^ d) := by
  rw [theta_eq_Psi M L D hM hD]
  simp only [Psi]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mem_Icc] at hd
  exact inner_sum_eq d M (by omega) L

private lemma sum_range_shift_two (N : ℕ) (f : ℕ → ℚ) :
    ∑ d ∈ Finset.range N, f (d + 2) = ∑ d ∈ Finset.Icc 2 (N + 1), f d := by
  induction N with
  | zero =>
      have h : Finset.Icc 2 1 = (∅ : Finset ℕ) := by
        ext i
        constructor
        · intro hi
          rw [Finset.mem_Icc] at hi
          omega
        · intro hi
          exact absurd hi (Finset.notMem_empty i)
      simp
  | succ N ih =>
      have hins : Finset.Icc 2 (N + 1 + 1) = insert (N + 2) (Finset.Icc 2 (N + 1)) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnm : (N + 2) ∉ Finset.Icc 2 (N + 1) := by
        simp only [Finset.mem_Icc]
        omega
      rw [Finset.sum_range_succ, ih, hins, Finset.sum_insert hnm]
      ring

/-- First displayed identity of `lem:odometer`, in the paper's literal
`∑_{d ≥ 2}` form (the index `d` below runs over `d + 2`, i.e. over `2, 3, …`).
All but finitely many terms vanish. -/
theorem theta_eq_tsum_divisorResidue (M L : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => (d + 2) ∣ M + i), (1 / 2 : ℚ) ^ i := by
  have hvan : ∀ d ∉ Finset.range (M + L),
      (∑ i ∈ (Finset.Icc 1 L).filter (fun i => (d + 2) ∣ M + i), (1 / 2 : ℚ) ^ i) = 0 := by
    intro d hd
    rw [Finset.mem_range, not_lt] at hd
    have hempty : (Finset.Icc 1 L).filter (fun i => (d + 2) ∣ M + i) = ∅ := by
      ext i
      constructor
      · intro hi
        rw [Finset.mem_filter, Finset.mem_Icc] at hi
        obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
        have hle := Nat.le_of_dvd (show 0 < M + i by omega) hi3
        omega
      · intro hi
        exact absurd hi (Finset.notMem_empty i)
    rw [hempty, Finset.sum_empty]
  rw [tsum_eq_sum hvan, theta_eq_Psi M L (M + L + 1) hM (by omega)]
  simp only [Psi]
  exact (sum_range_shift_two (M + L) _).symm

/-- Second displayed identity of `lem:odometer`, in the paper's literal
`∑_{d ≥ 2}` form. -/
theorem theta_eq_tsum_geometricForm (M L : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          (1 / 2 : ℚ) ^ (iLeast (d + 2) M)
            * (1 - (1 / 2 : ℚ) ^ ((d + 2) * mCount (d + 2) M L))
            / (1 - (1 / 2 : ℚ) ^ (d + 2)) := by
  have hvan : ∀ d ∉ Finset.range (M + L),
      ((1 / 2 : ℚ) ^ (iLeast (d + 2) M)
        * (1 - (1 / 2 : ℚ) ^ ((d + 2) * mCount (d + 2) M L))
        / (1 - (1 / 2 : ℚ) ^ (d + 2))) = 0 := by
    intro d hd
    rw [Finset.mem_range, not_lt] at hd
    have hmod : M % (d + 2) = M := Nat.mod_eq_of_lt (by omega)
    have hlt : L < iLeast (d + 2) M := by
      simp only [iLeast, hmod]
      omega
    exact geometric_term_eq_zero_of_lt_iLeast (d + 2) M L (by omega) hlt
  rw [tsum_eq_sum hvan, theta_eq_geometricForm M L (M + L + 1) hM hL (by omega)]
  exact (sum_range_shift_two (M + L) _).symm

/-! ### The closing "and nothing else" sentence: defect and correction -/

/-- CORRECTION, part one.  With the cutoff `D` fixed first, `Ψ_{L,D}` really is a
function of the residues of its argument modulo the `d` with `2 ≤ d ≤ D`, and
nothing else. -/
theorem Psi_eq_of_residues_eq (L D x y : ℕ) (h : ∀ d ∈ Finset.Icc 2 D, x % d = y % d) :
    Psi L D x = Psi L D y := by
  simp only [Psi]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hxy := h d hd
  have hset : (Finset.Icc 1 L).filter (fun i => d ∣ x + i)
      = (Finset.Icc 1 L).filter (fun i => d ∣ y + i) := by
    ext i
    simp only [Finset.mem_filter]
    refine and_congr_right (fun _ => ?_)
    have hmod : (x + i) % d = (y + i) % d := by
      rw [Nat.add_mod, Nat.add_mod y i, hxy]
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, hmod]
  rw [hset]

/-- CORRECTION, part two.  `Ψ_{L,D}` is periodic under any shift divisible by
every `d` with `2 ≤ d ≤ D`; in particular under `Q_D = lcm(1,…,D)`. -/
theorem Psi_add_of_forall_dvd (L D x N : ℕ) (hN : ∀ d ∈ Finset.Icc 2 D, d ∣ N) :
    Psi L D (x + N) = Psi L D x := by
  refine Psi_eq_of_residues_eq L D (x + N) x (fun d hd => ?_)
  obtain ⟨k, hk⟩ := hN d hd
  rw [hk, Nat.add_mul_mod_self_left]

/-- The residue determination transported back to `Θ`, with the cutoff dominating
both arguments.  True, but see `eq_of_residues_agree`: the hypothesis already
forces `x = y`, so this reading of the paper's sentence is vacuous. -/
theorem theta_eq_of_residues_eq (L D x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxD : x + L ≤ D) (hyD : y + L ≤ D)
    (h : ∀ d ∈ Finset.Icc 2 D, x % d = y % d) :
    Theta L x = Theta L y := by
  rw [theta_eq_Psi x L D hx hxD, theta_eq_Psi y L D hy hyD]
  exact Psi_eq_of_residues_eq L D x y h

/-- DEFECT WITNESS, vacuity half.  Agreement of all residues `mod d` for
`2 ≤ d ≤ D` between two positive integers `≤ D` already forces equality.  So
reading the lemma's last sentence with a cutoff dominating both arguments makes
it say nothing. -/
theorem eq_of_residues_agree (x y D : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxD : x ≤ D) (hyD : y ≤ D)
    (h : ∀ d ∈ Finset.Icc 2 D, x % d = y % d) : x = y := by
  have key : ∀ a b : ℕ, 1 ≤ a → b ≤ D → a ≤ b →
      (∀ d ∈ Finset.Icc 2 D, a % d = b % d) → a = b := by
    intro a b ha hbD hab hres
    by_contra hne
    have hlt : a < b := by omega
    have hd2 : 2 ≤ (b - a) + 1 := by omega
    have hdD : (b - a) + 1 ≤ D := by omega
    have hmod := hres ((b - a) + 1) (Finset.mem_Icc.mpr ⟨hd2, hdD⟩)
    have hmeq : Nat.ModEq ((b - a) + 1) a b := hmod
    have hdvd : ((b - a) + 1) ∣ (b - a) := (Nat.modEq_iff_dvd' hab).mp hmeq
    have hle := Nat.le_of_dvd (show 0 < b - a by omega) hdvd
    omega
  rcases le_total x y with hle | hle
  · exact key x y hx hyD hle h
  · exact (key y x hy hxD hle (fun d hd => (h d hd).symm)).symm

theorem theta_one_one : Theta 1 1 = 1 / 2 := by
  have h2 : ((Nat.divisors 2).card - 1 : ℕ) = 1 := by decide
  simp only [Theta, Finset.Icc_self, Finset.sum_singleton]
  norm_num [h2]

theorem theta_one_three : Theta 1 3 = 1 := by
  have h4 : ((Nat.divisors 4).card - 1 : ℕ) = 2 := by decide
  simp only [Theta, Finset.Icc_self, Finset.sum_singleton]
  norm_num [h4]

/-- DEFECT WITNESS, falsity half.  Read with one argument's own cutoff — the
reading the sentence "a function of the residues of `M` modulo every `d ≤ M+L`"
literally offers, since the cutoff moves with `M` — the claim is false:
at `M = 1`, `L = 1` the cutoff is `M + L = 2`, the integers `1` and `3` agree
modulo every `d ≤ 2`, and yet `Θ_1(1) = 1/2` while `Θ_1(3) = 1`. -/
theorem residue_cutoff_reading_fails :
    (∀ d ∈ Finset.Icc 2 (1 + 1), (1 : ℕ) % d = 3 % d) ∧ Theta 1 1 ≠ Theta 1 3 := by
  constructor
  · intro d hd
    rw [Finset.mem_Icc] at hd
    obtain ⟨hd1, hd2⟩ := hd
    have hd2' : d = 2 := by omega
    subst hd2'
    rfl
  · rw [theta_one_one, theta_one_three]
    norm_num

#print axioms residue_condition_iff
#print axioms iLeast_mem_Icc
#print axioms dvd_add_iLeast
#print axioms not_dvd_of_lt_iLeast
#print axioms iLeast_congr
#print axioms mCount_zero
#print axioms mCount_succ_of_dvd
#print axioms mCount_succ_of_not_dvd
#print axioms mCount_eq_div
#print axioms mCount_congr
#print axioms exponent_identity
#print axioms inner_sum_eq
#print axioms mCount_eq_zero_of_lt_iLeast
#print axioms geometric_term_eq_zero_of_lt_iLeast
#print axioms card_divisors_sub_one
#print axioms theta_eq_Psi
#print axioms theta_eq_divisorResidueSum
#print axioms theta_eq_geometricForm
#print axioms theta_eq_tsum_divisorResidue
#print axioms theta_eq_tsum_geometricForm
#print axioms Psi_eq_of_residues_eq
#print axioms Psi_add_of_forall_dvd
#print axioms theta_eq_of_residues_eq
#print axioms eq_of_residues_agree
#print axioms theta_one_one
#print axioms theta_one_three
#print axioms residue_cutoff_reading_fails

end ShortWindowDivisorPhase
end ErdosProblems.Erdos257.PaperCompleteR21
