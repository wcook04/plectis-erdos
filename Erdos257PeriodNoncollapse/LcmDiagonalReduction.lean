import Erdos257PeriodNoncollapse.CarrySurvivorExtinction

/-!
# Wave 23: the diagonal lcm collapse and the window structure of the lcm ray

Wave 22 collapsed the #249 supply throat onto the one-parameter period family
`H_t = lcm(1..t)` — but the position `N` stayed free: the supply hypothesis
still quantified over two unbounded parameters `(t, N)`.  This file removes
the second parameter.

**1. The diagonal collapse.**  Standing ON the ray, `N = H_t`, still beats
every hypothetical rational: a rational `S` has SOME primitive period `h₀`
and SOME pre-period `N₀`, and every `t ≥ max(h₀, N₀)` satisfies both
`h₀ ∣ H_t` and `H_t ≥ t ≥ N₀` at once.  So #249 follows from the SINGLE
ℕ-indexed sequence of decidable statements

  `P t := ∃ L, certifiedKill (periodLcm t) (periodLcm t) L`

holding for infinitely many `t`
(`irrational_totient_series_of_lcm_diagonal_certificate_supply`).  No second
parameter remains: one sequence, one predicate, decidable cell by cell.  The
survivor form lands alongside (`…_of_lcm_diagonal_survivor_supply`), as does
the general-position endpoint form (`…_of_lcm_certificate_supply`) — filling
the endpoint gap wave 22 left, where only the survivor version of the lcm
collapse existed.

**2. The window structure of the lcm ray.**  Why the diagonal is the right
place to stand: below `2t` EVERY window index divides the period except bare
prime powers in `(t, 2t)` (`eq_prime_pow_of_not_dvd_periodLcm`); indices
`j ≤ t` divide `lcm(1..t)` outright (`dvd_periodLcm`).  And on a clean
divisor `j` (every prime of `j` still divides `H/j`) the window totient
FACTORS exactly (`totient_periodLcm_ray_split`):

  `φ(q·H + j) = φ(j) · φ(q·(H/j) + 1)`,

splitting each window entry into a known local part `φ(j)` and a cofactor
totient whose argument is forced `≡ 1` mod every prime of `j`'s saturation.
The wave-23 probe (`build_erdos249_lcm_diagonal_shadow_probe.py`) decomposes
the exact tail difference along these classes against the Möbius–Mersenne
shadow constant `Σ_d μ(d)/(d·(2^d-1))`.

**Deposits.**  `certifiedKill_periodLcm_diagonal_upto_six` plus `_at_seven`
and `_at_eight` machine-check `P t` at the first eight scales — the
kernel-owned floor of the diagonal sequence; the probe extends the empirical
picture to `t = 32`.

The supply hypothesis `∀ t₀, ∃ t ≥ t₀, P t` is the open content of #249 and
is NOT claimed.  Everything here is elementary: lcm divisibility, totient
multiplicativity, geometric tails.  No q-Padé, no unformalised citations.
-/

set_option maxRecDepth 10000

namespace Erdos257PeriodNoncollapse
namespace TotientTailPeriodKiller

open Finset

/-! ## The scale sits below its own ray point: `t ≤ lcm(1..t)` -/

/-- Consecutive LCM heights are nested by divisibility. -/
theorem periodLcm_dvd_succ (t : ℕ) : periodLcm t ∣ periodLcm (t + 1) := by
  change periodLcm t ∣ Nat.lcm (periodLcm t) (t + 1)
  exact Nat.dvd_lcm_left _ _

/-- A strict LCM jump is at least as long as its starting height. -/
theorem periodLcm_strict_jump_sub_ge {t : ℕ}
    (hjump : periodLcm t < periodLcm (t + 1)) :
    periodLcm t ≤ periodLcm (t + 1) - periodLcm t := by
  obtain ⟨q, hq⟩ := periodLcm_dvd_succ t
  have hq2 : 2 ≤ q := by
    by_contra hnot
    have hqle : q ≤ 1 := by omega
    interval_cases q <;> simp_all
  apply Nat.le_sub_of_add_le
  calc
    periodLcm t + periodLcm t = periodLcm t * 2 := by omega
    _ ≤ periodLcm t * q := Nat.mul_le_mul_left _ hq2
    _ = periodLcm (t + 1) := hq.symm

lemma le_periodLcm (t : ℕ) : t ≤ periodLcm t := by
  cases t with
  | zero => exact Nat.zero_le _
  | succ n =>
      exact Nat.le_of_dvd (periodLcm_pos _) (dvd_periodLcm (by omega) le_rfl)

/-! ## The lcm endpoint collapse (general position) -/

/-- Endpoint-certificate variant of the wave-22 one-parameter collapse:
certified window kills along `lcm(1..t)` — arbitrarily large `t`, arbitrarily
large `N` — prove #249.  (Wave 22 landed only the survivor form.) -/
theorem irrational_totient_series_of_lcm_certificate_supply
    (hsupply : ∀ t₀ N₀ : ℕ,
      ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (periodLcm t) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_multiple_certificate_supply fun h₀ hpos N₀ => ?_
  obtain ⟨t, ht, N, hN, L, hkill⟩ := hsupply h₀ N₀
  have hdvd : h₀ ∣ periodLcm t := dvd_periodLcm hpos ht
  refine ⟨periodLcm t / h₀,
    Nat.div_pos (Nat.le_of_dvd (periodLcm_pos t) hdvd) hpos, N, hN, L, ?_⟩
  rwa [Nat.div_mul_cancel hdvd]

/-! ## The diagonal collapse: one parameter, one predicate -/

/-- **The wave-23 diagonal collapse.**  #249 follows from a SINGLE ℕ-indexed
sequence of decidable statements: the endpoint certificate firing on the
diagonal `(h, N) = (periodLcm t, periodLcm t)` for infinitely many `t`.
Rationality would supply a primitive period `h₀` and pre-period `N₀`; any
`t ≥ max(h₀, N₀)` gives `h₀ ∣ periodLcm t` and `periodLcm t ≥ t ≥ N₀`
simultaneously, so a diagonal kill at such `t` is a contradiction.  No second
parameter remains. -/
theorem irrational_totient_series_of_lcm_diagonal_certificate_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
      certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_lcm_certificate_supply fun t₀ N₀ => ?_
  obtain ⟨t, ht, L, hkill⟩ := hsupply (max t₀ N₀)
  exact ⟨t, le_trans (le_max_left _ _) ht, periodLcm t,
    le_trans (le_trans (le_max_right _ _) ht) (le_periodLcm t), L, hkill⟩

/-- Survivor variant of the diagonal collapse. -/
theorem irrational_totient_series_of_lcm_diagonal_survivor_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ K,
      survivorKill (periodLcm t) (periodLcm t) K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_lcm_survivor_supply fun t₀ N₀ => ?_
  obtain ⟨t, ht, K, hkill⟩ := hsupply (max t₀ N₀)
  exact ⟨t, le_trans (le_max_left _ _) ht, periodLcm t,
    le_trans (le_trans (le_max_right _ _) ht) (le_periodLcm t), K, hkill⟩

/-! ## Window structure: below `2t` the ray sees only divisors and bare prime powers -/

/-- **Window-structure theorem for the lcm ray.**  Below `2t`, the only
non-divisors of `lcm(1..t)` are bare prime powers exceeding `t`: every other
window index divides the period.  (Indices `j ≤ t` divide outright by
`dvd_periodLcm`; this pins down the sparse exceptional set above `t`.) -/
theorem eq_prime_pow_of_not_dvd_periodLcm {t j : ℕ} (hj : 0 < j) (hlt : j < 2 * t)
    (hnd : ¬ j ∣ periodLcm t) :
    ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j := by
  have htj : t < j := by
    by_contra hle
    exact hnd (dvd_periodLcm hj (not_lt.mp hle))
  have hH0 : periodLcm t ≠ 0 := (periodLcm_pos t).ne'
  have hfac : ¬ j.factorization ≤ (periodLcm t).factorization := fun hle =>
    hnd ((Nat.factorization_le_iff_dvd hj.ne' hH0).mp hle)
  simp only [Finsupp.le_def, not_forall, not_le] at hfac
  obtain ⟨p, hplt⟩ := hfac
  have hp : Nat.Prime p := by
    have hmem : p ∈ j.factorization.support := Finsupp.mem_support_iff.mpr (by omega)
    rw [Nat.support_factorization] at hmem
    exact Nat.prime_of_mem_primeFactors hmem
  set k := j.factorization p with hk
  set d := p ^ k with hd
  have hdvd_j : d ∣ j := by
    rw [hd, hk]
    exact Nat.ordProj_dvd j p
  have htpk : t < d := by
    by_contra hle
    have hdH : d ∣ periodLcm t :=
      dvd_periodLcm (pow_pos hp.pos _) (not_lt.mp hle)
    have hkle : k ≤ (periodLcm t).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hH0).mp hdH
    omega
  obtain ⟨m, hm⟩ := hdvd_j
  have hj2 : j < 2 * d := lt_of_lt_of_le hlt (Nat.mul_le_mul le_rfl htpk.le)
  have hm1 : m = 1 := by
    by_contra hm1
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hm
      omega
    have hm2 : 2 ≤ m := by omega
    have hge : 2 * d ≤ j := by
      rw [hm, mul_comm 2 d]
      exact Nat.mul_le_mul le_rfl hm2
    exact absurd hj2 (not_lt.mpr hge)
  exact ⟨p, k, hp, by rw [hm, hm1, mul_one, hd], htj⟩

/-! ## Ray factorisation: clean divisors split the window totient exactly -/

/-- If every prime of `j` divides `a`, then `j` and `q·a + 1` are coprime:
the cofactor is forced `≡ 1` mod every prime of `j`. -/
lemma coprime_ray_cofactor {j a : ℕ} (q : ℕ)
    (hcof : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ a) :
    Nat.Coprime j (q * a + 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpj : p ∣ j := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpm : p ∣ q * a + 1 := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hpqa : p ∣ q * a := (hcof p hp hpj).mul_left q
  have hp1 : p ∣ 1 := (Nat.dvd_add_right hpqa).mp hpm
  exact absurd (Nat.dvd_one.mp hp1) hp.one_lt.ne'

/-- Totient splits across the ray product `j·(q·a + 1)` whenever every prime
of `j` divides `a`. -/
theorem totient_ray_split {j a : ℕ} (q : ℕ)
    (hcof : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ a) :
    Nat.totient (j * (q * a + 1)) = Nat.totient j * Nat.totient (q * a + 1) :=
  Nat.totient_mul (coprime_ray_cofactor q hcof)

/-- **Lcm-ray window factorisation.**  For a clean divisor `j` of
`H = periodLcm t` — every prime of `j` still divides `H/j` — the window
totient at `q·H + j` splits into the KNOWN local part `φ(j)` and the cofactor
`φ(q·(H/j) + 1)`, whose argument avoids every prime of `j`'s saturation.
This is the exact identity behind the wave-23 shadow decomposition: on the
lcm ray the window is structured arithmetic, not totient noise. -/
theorem totient_periodLcm_ray_split {t j : ℕ} (q : ℕ) (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    Nat.totient (q * periodLcm t + j)
      = Nat.totient j * Nat.totient (q * (periodLcm t / j) + 1) := by
  have hjH : j * (periodLcm t / j) = periodLcm t := Nat.mul_div_cancel' hdvd
  have key : q * periodLcm t + j = j * (q * (periodLcm t / j) + 1) := by
    calc q * periodLcm t + j = q * (j * (periodLcm t / j)) + j := by rw [hjH]
      _ = j * (q * (periodLcm t / j) + 1) := by ring
  rw [key]
  exact totient_ray_split q hclean

/-- **Recursive lcm-ray quotient identity.**  After removing the exact clean
factor `φ(j)`, an lcm-ray forcing letter is another genuine `deltaTotient`
letter at the smaller scale `periodLcm t / j`.  Thus the factor is only the
outer gauge; the quotient retains arithmetic information that homogeneous
divisibility alone discards. -/
theorem deltaTotient_periodLcm_ray_split {t j : ℕ} (q : ℕ)
    (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    deltaTotient (periodLcm t) (q * periodLcm t + j) =
      (Nat.totient j : ℤ) *
        deltaTotient (periodLcm t / j)
          (q * (periodLcm t / j) + 1) := by
  unfold deltaTotient
  rw [show q * periodLcm t + j + periodLcm t =
        (q + 1) * periodLcm t + j by ring]
  rw [totient_periodLcm_ray_split (q + 1) hdvd hclean,
    totient_periodLcm_ray_split q hdvd hclean]
  push_cast
  ring_nf

/-! ## Kernel-decided diagonal deposits: the floor of the sequence `P t` -/

/-- Certified diagonal kill depths for `1 ≤ t ≤ 8`, matching the wave-23
probe (`lcm_diagonal_shadow_probe.json`). -/
def diagonalKillDepth : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 6 => 9
  | 7 => 14
  | 8 => 15
  | _ => 0

/-- **Diagonal deposit.**  The wave-23 predicate `P t` holds for every
`1 ≤ t ≤ 6`: the endpoint certificate fires at `(H_t, H_t)` with the
tabulated depth.  Totient arguments stay ≤ 130 — a light kernel `decide`. -/
theorem certifiedKill_periodLcm_diagonal_upto_six :
    ∀ t ∈ Finset.Icc 1 6,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalKillDepth t) := by decide

/-- `P 7`: the diagonal certificate at `lcm(1..7) = 420`, depth `14`. -/
theorem certifiedKill_periodLcm_diagonal_at_seven :
    certifiedKill (periodLcm 7) (periodLcm 7) 14 := by decide

/-- `P 8`: the diagonal certificate at `lcm(1..8) = 840`, depth `15`. -/
theorem certifiedKill_periodLcm_diagonal_at_eight :
    certifiedKill (periodLcm 8) (periodLcm 8) 15 := by decide

/-- No lcm-diagonal tail difference is an integer at the first six scales:
`D_{H_t}(H_t) ∉ ℤ` for `1 ≤ t ≤ 6`. -/
theorem tail_diff_not_int_periodLcm_diagonal (t : ℕ) (h1 : 1 ≤ t) (h6 : t ≤ 6) :
    totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
      ∉ Set.range ((↑) : ℤ → ℝ) :=
  tail_diff_notMem_int_of_certifiedKill
    (certifiedKill_periodLcm_diagonal_upto_six t (Finset.mem_Icc.mpr ⟨h1, h6⟩))

end TotientTailPeriodKiller
end Erdos257PeriodNoncollapse
