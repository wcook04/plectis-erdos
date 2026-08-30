import Erdos249257.TotientTailPeriodKiller
import Erdos249257.LcmConeFlatness
import ErdosProblems.Erdos249.CyclotomicAnchoredKill

/-!
# Depth = period: the period-multiple kill supply

Erdős #249 asks whether `S = ∑ φ(n)/2^n` is irrational.  The certificate
engine (`certifiedKill`) and its soundness/completeness are landed; this file
adds the **ray-restricted normal form** that the cyclotomic-fan analysis
converges to, plus the first denominator deposits beyond the 64-smooth
diagonal bank.

## The depth = period cut

For the two-block integer `W(h,N) = Q_{h,N+h} - Q_{h,N}` (which is exactly
`windowDiscrepancy h N h`), the block law at heights `h` gives the real
identity `W = 2^h·δ_h(N) - δ_h(N+h)` with `δ_h(M) = R_{M+h} - R_M`.  If `S`
is rational with denominator `2^c·v` (`v` odd) then for every multiple `h`
of a period of `v` and every `N ≥ c` both `δ`'s are integers, so
`W ≡ -δ_h(N+h) (mod 2^h)` with `|δ_h(N+h)| < N+2h+2`: the residue is pinned
to the two edge arcs.  A central residue — `certifiedKill h N h` — refutes
that denominator class outright.  The unknown odd part `v` enters only
through the arithmetic progression of admissible `h`, never the modulus.

## The supply normal form

`PeriodMultipleKillSupply` demands, for every ray `d` and every basepoint
threshold `c`, one certified kill at some period `t·d` and some `N ≥ c`
(any depth `L`).  This is **exactly equivalent** to irrationality:
sufficiency composes the Euler tail-period law with a telescoping step, and
necessity is certificate completeness.  `ApFullDepthEscape` is the
depth-locked (`L = h`) variant: sufficient, and the cleanest single open
statement this programme has produced, but not known necessary.

## Nesting (the fan collapses onto the dyadic tower)

`totientBlock_add` is the concatenation identity
`Q_{a+b,N} = 2^b·Q_{a,N} + Q_{b,N+a}`.  It makes the order-4 cyclotomic
channel at height `h` literally the order-2 channel at height `2h`
(`Ψ₄(2^h) = 2^{2h}+1 = Ψ₂(2^{2h})`), so the 2–3–4 fan is a nested family of
depth = period tests along the tower `h, 2h, 4h, …`, not three unrelated
moduli.

## New deposits

The diagonal bank certifies kills at `periodLcm t = lcm(1..t)` through
`t = 64` (`certifiedKill_diagonal_t64`), covering every odd `v` whose
multiplicative order of 2 divides `lcm(1..64)`.  The first prime-power
periods it cannot reach are `67, 81, 97, 101, 121, 125, 127, 128`.  This
file certifies kills at all eight (basepoint `N = 300`), each yielding the
denominator exclusion `S ≠ r` for `r.den ∣ 2^300·(2^h - 1)` — new odd
classes including the Cole factors `2^67 - 1 = 193707721 · 761838257287`
and the Mersenne prime `2^127 - 1`.
-/

namespace ErdosProblems.Erdos249.PeriodMultipleEscape

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.CyclotomicAnchoredKill

/-! ## Bridge and nesting identities -/

/-- **Depth = period bridge.**  The full-depth window discrepancy is the
difference of two adjacent period blocks: `W(h,N) = Q_{h,N+h} - Q_{h,N}`. -/
theorem windowDiscrepancy_self_eq_totientBlock_sub (h N : ℕ) :
    windowDiscrepancy h N h = totientBlock h (N + h) - totientBlock h N := by
  unfold windowDiscrepancy totientBlock
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_mul]

/-- **Block concatenation.**  `Q_{a+b,N} = 2^b·Q_{a,N} + Q_{b,N+a}`.  This is
the identity that nests the cyclotomic fan: the order-4 channel at height `h`
is the order-2 channel at height `2h`. -/
theorem totientBlock_add (a b N : ℕ) :
    totientBlock (a + b) N = 2 ^ b * totientBlock a N + totientBlock b (N + a) := by
  unfold totientBlock
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < a := Finset.mem_range.mp hj
    have hexp : a + b - 1 - j = b + (a - 1 - j) := by omega
    rw [hexp, pow_add]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    have harg : N + 1 + (a + i) = N + a + 1 + i := by omega
    have hexp : a + b - 1 - (a + i) = b - 1 - i := by omega
    rw [harg, hexp]

/-! ## Pure-dyadic endpoint-error cocycle -/

/- The signed error after subtracting one fixed integer multiple of the
Mersenne modulus.  On an endpoint-trapped pure-dyadic trajectory, the nearest
integer multiplier is fixed and this is the small coordinate seen by the
canonical residue-gap consumer. -/
def pureDyadicEndpointError (H c : ℕ) (k : ℤ) : ℤ :=
  totientBlock H c - k * ((2 : ℤ) ^ H - 1)

/- Extending a totient block by one letter doubles the old block and appends
the new totient letter. -/
theorem totientBlock_height_succ (H c : ℕ) :
    totientBlock (H + 1) c =
      2 * totientBlock H c + (Nat.totient (c + H + 1) : ℤ) := by
  rw [totientBlock_add H 1 c]
  simp [totientBlock]

/- The recurrence used by the excursion theorem. -/
theorem pureDyadicEndpointError_succ (H c : ℕ) (k : ℤ) :
    pureDyadicEndpointError (H + 1) c k =
      2 * pureDyadicEndpointError H c k +
        (Nat.totient (c + H + 1) : ℤ) - k := by
  rw [pureDyadicEndpointError, pureDyadicEndpointError,
    totientBlock_height_succ, pow_succ]
  ring

/- **Prime-position excursion inequality.**  If the next actual totient
letter is evaluated at a prime, then a fixed-quotient endpoint error must pay
for that prime through one of two adjacent error coordinates.

This deletes every bounded or sublinear version of the inhomogeneous boundary
mode: along arbitrarily large shifted primes, the right side must have linear
size.  Any permanent endpoint trap that remains possible must therefore use
the full linear moving envelope, rather than shadowing a bounded perturbation
of the homogeneous constant-two mode. -/
theorem prime_forces_pureDyadicEndpointError_excursion
    (H c : ℕ) (k : ℤ) (hp : Nat.Prime (c + H + 1)) :
    (c + H : ℤ) - k ≤
      |pureDyadicEndpointError (H + 1) c k| +
        2 * |pureDyadicEndpointError H c k| := by
  have hrec := pureDyadicEndpointError_succ H c k
  have hphi : (Nat.totient (c + H + 1) : ℤ) = (c + H : ℤ) := by
    rw [Nat.totient_prime hp]
    omega
  rw [hphi] at hrec
  have hnext := le_abs_self (pureDyadicEndpointError (H + 1) c k)
  have hcurrent := neg_le_abs (pureDyadicEndpointError H c k)
  linarith

/- Prime-position excursions occur beyond every requested height.  This is
the cofinal, actual-word form of
`prime_forces_pureDyadicEndpointError_excursion`; it consumes Euclid's
unbounded-prime supply rather than any pointwise description of totient
values. -/
theorem exists_late_pureDyadicEndpointError_excursion
    (c B : ℕ) (k : ℤ) :
    ∃ H, B ≤ H ∧
      (c + H : ℤ) - k ≤
        |pureDyadicEndpointError (H + 1) c k| +
          2 * |pureDyadicEndpointError H c k| := by
  obtain ⟨p, hpLower, hpPrime⟩ :=
    Nat.exists_infinite_primes (c + B + 1)
  refine ⟨p - (c + 1), ?_, ?_⟩
  · omega
  · have hindex : c + (p - (c + 1)) + 1 = p := by omega
    have hpShift : Nat.Prime (c + (p - (c + 1)) + 1) := by
      simpa only [hindex] using hpPrime
    exact prime_forces_pureDyadicEndpointError_excursion
      (p - (c + 1)) c k hpShift

/- **Prime-successor bottom lock.**  Suppose `p = c+H+1` is prime and the
error remains below the upper endpoint boundary for one further step.  The
two consecutive actual totient letters then force the error immediately
before `p` into an explicit lower linear half-space.

Unlike the adjacent absolute-value excursion bound, this is directional: a
permanent endpoint trap cannot answer large prime letters by alternating
arbitrarily.  Immediately before each prime whose successor is still trapped,
it must satisfy this bottom-lock inequality. -/
theorem prime_successor_upper_trap_forces_bottom_lock
    (H c : ℕ) (k : ℤ) (hp : Nat.Prime (c + H + 1))
    (hupper :
      pureDyadicEndpointError (H + 2) c k ≤ (c + H + 3 : ℤ)) :
    4 * pureDyadicEndpointError H c k + (c + H + 1 : ℤ) +
        (Nat.totient (c + H + 2) : ℤ) ≤ 4 + 3 * k := by
  have hprime := pureDyadicEndpointError_succ H c k
  have hsuccessor := pureDyadicEndpointError_succ (H + 1) c k
  have hphi : (Nat.totient (c + H + 1) : ℤ) = (c + H : ℤ) := by
    rw [Nat.totient_prime hp]
    omega
  rw [hphi] at hprime
  have hsuccessorIndex : c + (H + 1) + 1 = c + H + 2 := by omega
  rw [hsuccessorIndex] at hsuccessor
  linarith

/- Cofinal form of the directional prime-successor constraint.  If the
upper endpoint boundary traps every height, then beyond every cutoff there is
a prime precursor satisfying the exact bottom-lock inequality. -/
theorem exists_late_prime_predecessor_bottom_lock_of_upper_trap
    (c B : ℕ) (k : ℤ)
    (hupper : ∀ J, pureDyadicEndpointError J c k ≤ (c + J + 1 : ℤ)) :
    ∃ H, B ≤ H ∧ Nat.Prime (c + H + 1) ∧
      4 * pureDyadicEndpointError H c k + (c + H + 1 : ℤ) +
          (Nat.totient (c + H + 2) : ℤ) ≤ 4 + 3 * k := by
  obtain ⟨p, hpLower, hpPrime⟩ :=
    Nat.exists_infinite_primes (c + B + 1)
  refine ⟨p - (c + 1), ?_, ?_, ?_⟩
  · omega
  · simpa only [show c + (p - (c + 1)) + 1 = p by omega] using hpPrime
  · apply prime_successor_upper_trap_forces_bottom_lock
      (p - (c + 1)) c k
    · simpa only [show c + (p - (c + 1)) + 1 = p by omega] using hpPrime
    · exact hupper (p - (c + 1) + 2)

/-- Doubling instance of concatenation: the two `2h`-blocks entering the
order-2 test at height `2h` are built from the four `h`-blocks of the fan. -/
theorem totientBlock_two_mul (h N : ℕ) :
    totientBlock (2 * h) N = 2 ^ h * totientBlock h N + totientBlock h (N + h) := by
  simpa [two_mul] using totientBlock_add h h N

/-! ## The period-multiple kill supply -/

/-- Integrality of the step tail difference from `N₀` on telescopes to every
multiple of the period. -/
theorem tail_diff_mul_mem_int_of_forall_step {h₀ N₀ : ℕ}
    (hint : ∀ N, N₀ ≤ N →
      totientTail (N + h₀) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∀ t N, N₀ ≤ N →
      totientTail (N + t * h₀) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  intro t
  induction t with
  | zero => intro N _; exact ⟨0, by simp⟩
  | succ t ih =>
      intro N hN
      obtain ⟨a, ha⟩ := ih N hN
      obtain ⟨b, hb⟩ := hint (N + t * h₀) (le_trans hN (Nat.le_add_right _ _))
      refine ⟨b + a, ?_⟩
      have harr : N + (t + 1) * h₀ = N + t * h₀ + h₀ := by ring
      rw [harr]
      push_cast
      linarith [ha, hb]

/-- **The supply normal form.**  For every ray `d ≥ 1` and every basepoint
threshold `c`, some multiple period `t·d` admits a certified kill at some
`N ≥ c`.  The odd part of a hypothetical denominator selects the ray; the
kill contradicts the tail-period law on it. -/
def PeriodMultipleKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L

/-- **Supply ⇒ irrationality.**  Rationality yields a period `h₀` with the
step tail difference integral from `N₀` on; telescoping makes every multiple
period integral there; the supplied kill on the ray of `h₀` is a
contradiction. -/
theorem irrational_totient_series_of_periodMultipleKillSupply
    (hsupply : PeriodMultipleKillSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h₀, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨t, N, L, ht, hN, hkill⟩ := hsupply h₀ hpos N₀
  exact tail_diff_notMem_int_of_certifiedKill hkill
    (tail_diff_mul_mem_int_of_forall_step hint t N hN)

/-- **Irrationality ⇒ supply** (certificate completeness on each ray, at
`t = 1` and the exact basepoint). -/
theorem periodMultipleKillSupply_of_irrational
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    PeriodMultipleKillSupply := by
  intro d hd c
  obtain ⟨L, hL⟩ := exists_certifiedKill_of_tail_diff_notMem_int
    (irrational_totient_series_iff_all_tail_diffs_nonintegral.mp hirr d hd c)
  exact ⟨1, c, L, Nat.one_pos, le_rfl, by simpa using hL⟩

/-- **The exact open core of #249 in ray form.**  The period-multiple kill
supply is not a sufficient surrogate: it is equivalent to irrationality. -/
theorem periodMultipleKillSupply_iff_irrational :
    PeriodMultipleKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨irrational_totient_series_of_periodMultipleKillSupply,
    periodMultipleKillSupply_of_irrational⟩

/-- **Depth = period escape (locked depth `L = h`).**  The single-inequality
form: on every ray and at every basepoint, some multiple period is central at
its own depth.  Sufficient for irrationality; not known necessary. -/
def ApFullDepthEscape : Prop :=
  ∀ d : ℕ, 0 < d → ∀ N : ℕ, ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)

theorem periodMultipleKillSupply_of_apFullDepthEscape
    (h : ApFullDepthEscape) : PeriodMultipleKillSupply := by
  intro d hd c
  obtain ⟨t, ht, hkill⟩ := h d hd c
  exact ⟨t, c, t * d, ht, le_rfl, hkill⟩

theorem irrational_totient_series_of_apFullDepthEscape
    (h : ApFullDepthEscape) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_periodMultipleKillSupply
    (periodMultipleKillSupply_of_apFullDepthEscape h)

/-! ## Deposits: the first periods beyond the 64-smooth diagonal ceiling -/

/-- Any certified kill yields the denominator exclusion for its period ray
and basepoint.  Generic form of the `30_300` instance. -/
theorem totient_series_ne_rat_of_certifiedKill {h N L : ℕ}
    (hkill : certifiedKill h N L) (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := fun hS =>
  tail_diff_notMem_int_of_certifiedKill hkill
    (tail_diff_int_of_den_dvd r hS h N hdvd)

set_option maxRecDepth 100000

/-- Period 67 (prime, first past the diagonal bank), residue `1654` in
`(380, 2^11 - 380)`. -/
theorem certifiedKill_67_300 : certifiedKill 67 300 11 := by decide

/-- Period 81 = 3⁴ (the bank holds only 3³ ∣ lcm(1..64)), residue `540`. -/
theorem certifiedKill_81_300 : certifiedKill 81 300 13 := by decide

/-- Period 97 (prime), residue `7616`. -/
theorem certifiedKill_97_300 : certifiedKill 97 300 13 := by decide

/-- Period 101 (prime), residue `1270`. -/
theorem certifiedKill_101_300 : certifiedKill 101 300 11 := by decide

/-- Period 121 = 11² (the bank holds only 11¹), residue `478`. -/
theorem certifiedKill_121_300 : certifiedKill 121 300 10 := by decide

/-- Period 125 = 5³ (the bank holds only 5²), residue `762`. -/
theorem certifiedKill_125_300 : certifiedKill 125 300 18 := by decide

/-- Period 127 (prime; `2^127 - 1` is itself the Mersenne prime M127),
residue `530`. -/
theorem certifiedKill_127_300 : certifiedKill 127 300 11 := by decide

/-- Period 128 = 2⁷ (the bank holds only 2⁶), residue `1552`. -/
theorem certifiedKill_128_300 : certifiedKill 128 300 11 := by decide

/-- **Depth = period flagship.**  The period-67 kill at its own depth
`L = h = 67`: the locked-depth certificate `ApFullDepthEscape` demands, made
concrete at one point of the `d = 67` ray. -/
theorem certifiedKill_67_300_fullDepth : certifiedKill 67 300 67 := by decide

/-! Denominator exclusions.  Each covers every rational whose denominator is
`2^c·v` with `c ≤ 300` and `v ∣ 2^h - 1` — ord-2 classes outside every
previously certified period. -/

theorem totient_series_ne_rat_of_den_dvd_67_300 (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 67 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_certifiedKill certifiedKill_67_300 r hdvd

theorem totient_series_ne_rat_of_den_dvd_81_300 (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 81 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_certifiedKill certifiedKill_81_300 r hdvd

theorem totient_series_ne_rat_of_den_dvd_97_300 (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 97 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_certifiedKill certifiedKill_97_300 r hdvd

theorem totient_series_ne_rat_of_den_dvd_101_300 (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 101 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_certifiedKill certifiedKill_101_300 r hdvd

theorem totient_series_ne_rat_of_den_dvd_121_300 (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 121 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_certifiedKill certifiedKill_121_300 r hdvd

theorem totient_series_ne_rat_of_den_dvd_125_300 (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 125 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_certifiedKill certifiedKill_125_300 r hdvd

theorem totient_series_ne_rat_of_den_dvd_127_300 (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 127 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_certifiedKill certifiedKill_127_300 r hdvd

theorem totient_series_ne_rat_of_den_dvd_128_300 (r : ℚ)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 300 * (2 ^ 128 - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) :=
  totient_series_ne_rat_of_certifiedKill certifiedKill_128_300 r hdvd

#print axioms windowDiscrepancy_self_eq_totientBlock_sub
#print axioms totientBlock_add
#print axioms pureDyadicEndpointError_succ
#print axioms prime_forces_pureDyadicEndpointError_excursion
#print axioms exists_late_pureDyadicEndpointError_excursion
#print axioms prime_successor_upper_trap_forces_bottom_lock
#print axioms exists_late_prime_predecessor_bottom_lock_of_upper_trap
#print axioms irrational_totient_series_of_periodMultipleKillSupply
#print axioms periodMultipleKillSupply_iff_irrational
#print axioms irrational_totient_series_of_apFullDepthEscape
#print axioms certifiedKill_67_300_fullDepth
#print axioms totient_series_ne_rat_of_den_dvd_127_300

end ErdosProblems.Erdos249.PeriodMultipleEscape
