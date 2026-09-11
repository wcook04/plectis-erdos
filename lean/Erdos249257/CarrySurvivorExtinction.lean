import Erdos249257.TotientTailPeriodKiller

/-!
# Wave 22: carry-survivor extinction and the multiple-period collapse

Wave 21 reduced #249 to a certified kill supply: for every period `h ≥ 1` and
every threshold `N₀`, some `(N ≥ N₀, L)` with the endpoint residue certificate
`certifiedKill h N L`.  This file spends two further consequences of
rationality that the wave-21 socket left on the table.

**1. The multiple-period collapse.**  If `h₀` is an eventual binary period,
every multiple `m·h₀` is too, by pure telescoping:

  `D_{m·h}(N) = ∑_{i<m} D_h(N + i·h)`,   `D_h(N) = R_{N+h} - R_N`.

So the supply obligation weakens from *kill every `h`* to *kill one multiple
per divisibility ray* (`irrational_totient_series_of_multiple_survivor_supply`)
— and further collapses onto the ONE-PARAMETER family `lcm(1..t)`, since every
`h₀ ≤ t` divides `lcm(1..t)`
(`irrational_totient_series_of_lcm_survivor_supply`).  The throat of #249
narrows from a ∀h family of targets to a single ℕ-indexed ray.

**2. The carry-survivor certificate.**  The wave-21 note called the
bounded-orbit reformulation advisory.  Here it is machine-checked: doubling
the tail shifts the window by one and expels the head totient
(`totientTail_succ`), so an integer tail difference `d = D_h(N)` launches the
exact integer orbit

  `orbit 0 = d`,  `orbit (i+1) = 2·orbit i - (φ(N+i+1+h) - φ(N+i+1))`,

which tracks `D_h(N+i)` forever (`carryOrbit_eq_tail_diff`) and is therefore
trapped in the strip `|·| < N+i+h+2` (`abs_tail_diff_lt`).  The certificate
`survivorKill h N K` checks — finitely, decidably — that every integer
candidate in the initial box escapes the strip within `K` steps; soundness is
`tail_diff_notMem_int_of_survivorKill`.  The survivor predicate is strictly
stronger than the endpoint certificate at equal depth
(`survivor_strict_at_equal_budget`, a `decide` witness at `(1, 57, 8)`), but
the wave-22 probe measures the two families as near-equivalent in minimal
kill depth — the deepest scale dominates.  The probe's honest summary: the
multiple-period loosening is the logical gain; the survivor form is the
bounded-orbit lane made kernel-checkable.

**Deposits.**  `certifiedKill_all_upto_sixteen` machine-checks kills for every
`h ≤ 16` at `(N, L) = (14, 9)` — twice the wave-21 period range in a smaller
window — giving the extended exclusion
`totient_series_ne_rat_of_den_dvd_upto_sixteen`: `S` is no rational whose
denominator divides `2¹⁴·(2ʰ-1)` for any `h ≤ 16`.

Everything remains elementary: `φ(n) ≤ n`, geometric tails, integer orbit
arithmetic.  No q-Padé, no Stern–Brocot, no unformalised citations.
-/

set_option maxRecDepth 10000

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-! ## Tail bounds: the strip that traps every integer carry orbit -/

/-- The local totient tail is strictly positive. -/
lemma totientTail_pos (M : ℕ) : 0 < totientTail M := by
  have hle : (Nat.totient (M + 1 + 0) : ℝ) / 2 ^ (0 + 1) ≤ totientTail M :=
    (summable_totientTail_terms M).le_tsum 0 fun j _ => by positivity
  have h1 : 0 < Nat.totient (M + 1 + 0) := Nat.totient_pos.mpr (by omega)
  have h1' : (0 : ℝ) < (Nat.totient (M + 1 + 0) : ℝ) := by exact_mod_cast h1
  have hpos : (0 : ℝ) < (Nat.totient (M + 1 + 0) : ℝ) / 2 ^ (0 + 1) := by positivity
  linarith

/-- `R_M ≤ M + 2`: the window bound at depth `0`. -/
lemma totientTail_le (M : ℕ) : totientTail M ≤ (M : ℝ) + 2 := by
  have h := tail_after_le M 0
  simp only [add_zero, pow_zero, Nat.cast_zero, div_one] at h
  exact h

/-- The tail difference `D_h(N) = R_{N+h} - R_N` is trapped in the open strip
`|D_h(N)| < N + h + 2`. -/
lemma abs_tail_diff_lt (h N : ℕ) :
    |totientTail (N + h) - totientTail N| < (N : ℝ) + h + 2 := by
  have h1 := totientTail_pos (N + h)
  have h2 := totientTail_pos N
  have h3 := totientTail_le (N + h)
  have h4 := totientTail_le N
  push_cast at h3
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  rw [abs_lt]
  constructor <;> linarith

/-! ## The carry recurrence -/

/-- **Carry recurrence.**  `R_{M+1} = 2·R_M - φ(M+1)`: doubling the tail shifts
the window by one and expels the head totient. -/
lemma totientTail_succ (M : ℕ) :
    totientTail (M + 1) = 2 * totientTail M - (Nat.totient (M + 1) : ℝ) := by
  have hsum := summable_totientTail_terms M
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hhead : ∑ j ∈ Finset.range 1, (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1)
      = (Nat.totient (M + 1) : ℝ) / 2 := by
    rw [Finset.sum_range_one]
    norm_num
  have htail : ∑' j : ℕ, (Nat.totient (M + 1 + (j + 1)) : ℝ) / 2 ^ ((j + 1) + 1)
      = totientTail (M + 1) / 2 := by
    unfold totientTail
    rw [← tsum_div_const]
    exact tsum_congr fun j => by
      rw [show M + 1 + (j + 1) = M + 1 + 1 + j from by omega, div_div, ← pow_succ]
  have hkey : (Nat.totient (M + 1) : ℝ) / 2 + totientTail (M + 1) / 2 = totientTail M := by
    calc (Nat.totient (M + 1) : ℝ) / 2 + totientTail (M + 1) / 2
        = (∑ j ∈ Finset.range 1, (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1))
          + ∑' j : ℕ, (Nat.totient (M + 1 + (j + 1)) : ℝ) / 2 ^ ((j + 1) + 1) := by
          rw [hhead, htail]
      _ = totientTail M := hsplit
  linarith

/-- **Exact tail-window split.**  The first `L` binary digits of `R_M` are
the finite window already used by the certificate kernel; the remaining
endpoint is exactly `2⁻ᴸ R_{M+L}`.  This is the general coboundary identity
behind every later sliding-suffix specialization. -/
lemma totientTail_eq_partial_add_shifted (M L : ℕ) :
    totientTail M
      = (∑ j ∈ Finset.range L,
          (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1))
        + totientTail (M + L) / 2 ^ L := by
  rw [totientTail_eq_partial_add_tail]
  congr 1
  unfold totientTail
  rw [← tsum_div_const]
  refine tsum_congr fun j => ?_
  rw [show M + 1 + (j + L) = M + L + 1 + j by omega,
    show (j + L) + 1 = (j + 1) + L by omega, pow_add,
    div_mul_eq_div_div]

/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. -/
def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)

/-- The fresh totient forcing letter is bounded by its later argument.  This is
the arithmetic input that makes the depth barrier strict: at depth `L` the
new letter has size at most `N + h + L + 1`, one less than the endpoint
corridor radius. -/
lemma abs_deltaTotient_le (h n : ℕ) :
    |deltaTotient h n| ≤ (n + h : ℕ) := by
  unfold deltaTotient
  rw [abs_le]
  constructor
  · have hφn : (Nat.totient n : ℤ) ≤ n := by exact_mod_cast Nat.totient_le n
    have hφnh_nonneg : (0 : ℤ) ≤ Nat.totient (n + h) := by positivity
    push_cast
    omega
  · have hφnh : (Nat.totient (n + h) : ℤ) ≤ n + h := by
      exact_mod_cast Nat.totient_le (n + h)
    have hφn_nonneg : (0 : ℤ) ≤ Nat.totient n := by positivity
    push_cast
    omega

/-- **Exact depth recurrence for the endpoint word.**  Increasing certificate
depth doubles the existing signed window and appends exactly one fresh
totient-difference letter.  This is a depth recurrence with explicit input,
not the autonomous temporal recurrence ruled out by the finite-state no-go. -/
lemma windowDiscrepancy_succ (h N L : ℕ) :
    windowDiscrepancy h N (L + 1)
      = 2 * windowDiscrepancy h N L + deltaTotient h (N + L + 1) := by
  unfold windowDiscrepancy deltaTotient
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hjL : j < L := Finset.mem_range.mp hj
    rw [show L - j = (L - 1 - j) + 1 by omega, pow_succ]
    ring
  · simp only [Nat.sub_self, pow_zero, mul_one]
    rw [show N + h + 1 + L = N + L + 1 + h by omega,
      show N + 1 + L = N + L + 1 by omega]

/-- **Exact spatial recurrence for a fixed-depth window.**  Sliding the base
from `N` to `N+1` expels the head letter with weight `2^L`, doubles the old
window, and appends one fresh endpoint letter.  Modulo `2^L` only the doubled
residue and the fresh endpoint remain.  The natural bound
`abs_deltaTotient_le` already places that endpoint inside the certificate
corridor, so this identity alone is not a one-step anti-trapping theorem. -/
theorem windowDiscrepancy_slide (h N L : ℕ) :
    windowDiscrepancy h (N + 1) L =
      2 * windowDiscrepancy h N L
      - deltaTotient h (N + 1) * 2 ^ L
      + deltaTotient h (N + L + 1) := by
  induction L with
  | zero =>
      simp [windowDiscrepancy]
  | succ L ih =>
      rw [windowDiscrepancy_succ, windowDiscrepancy_succ, ih, pow_succ]
      rw [show N + 1 + L + 1 = N + (L + 1) + 1 by omega]
      ring

/-- **Depth barrier.**  Once an endpoint certificate fires, every deeper
window fires as well.  The proof uses the exact input-driven recurrence and
the strict totient bound; no finite state or empirical residue table enters.
Equivalently, endpoint survival is prefix-closed in certificate depth. -/
theorem certifiedKill_succ {h N L : ℕ} (hcert : certifiedKill h N L) :
    certifiedKill h N (L + 1) := by
  rcases hcert with ⟨hlow, hhigh⟩
  set B : ℤ := N + h + L + 2
  set P : ℤ := 2 ^ L
  set A : ℤ := windowDiscrepancy h N L
  set r : ℤ := A % P
  set d : ℤ := deltaTotient h (N + L + 1)
  have hPpos : 0 < P := by simp [P]
  have hdabs : |d| ≤ B - 1 := by
    have hd := abs_deltaTotient_le h (N + L + 1)
    dsimp [d, B]
    push_cast at hd ⊢
    omega
  have hd := abs_le.mp hdabs
  have hx0 : 0 ≤ 2 * r + d := by
    change B < r at hlow
    linarith
  have hxP : 2 * r + d < P * 2 := by
    change r < P - B at hhigh
    linarith
  have hAdiv : P * (A / P) + r = A := by
    change P * (A / P) + A % P = A
    exact Int.mul_ediv_add_emod A P
  have hrewrite : 2 * A + d = P * (2 * (A / P)) + (2 * r + d) := by
    linarith
  have hmod : (2 * A + d) % (P * 2) = 2 * r + d := by
    rw [hrewrite]
    have hmul : P * (2 * (A / P)) = (P * 2) * (A / P) := by ring
    rw [hmul, show (P * 2) * (A / P) + (2 * r + d)
        = (2 * r + d) + (P * 2) * (A / P) by ring,
      Int.add_mul_emod_self_left, Int.emod_eq_of_lt hx0 hxP]
  unfold certifiedKill
  rw [windowDiscrepancy_succ, show (2 : ℤ) ^ (L + 1) = P * 2 by simp [P, pow_succ]]
  change B + 1 < (2 * A + d) % (P * 2) ∧
    (2 * A + d) % (P * 2) < P * 2 - (B + 1)
  rw [hmod]
  change B < r at hlow
  change r < P - B at hhigh
  constructor <;> linarith

/-- A successful depth is an absorbing proof state: appending any finite
suffix of the totient forcing word cannot recreate an endpoint survivor. -/
theorem certifiedKill_add {h N L : ℕ} (hcert : certifiedKill h N L) :
    ∀ k : ℕ, certifiedKill h N (L + k) := by
  intro k
  induction k with
  | zero => simpa using hcert
  | succ k ih =>
      simpa [Nat.add_assoc] using certifiedKill_succ ih

/-- The signed endpoint-survivor fibre at depth `L`.  Its elements are the
integer representatives of the exact discrepancy residue that still fit in
the analytic endpoint corridor. -/
def endpointSurvivor (h N L : ℕ) (z : ℤ) : Prop :=
  |z| ≤ (N + h + L + 2 : ℤ) ∧
    z % 2 ^ L = windowDiscrepancy h N L % 2 ^ L

instance (h N L : ℕ) (z : ℤ) : Decidable (endpointSurvivor h N L z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A central-arc certificate empties the signed endpoint-survivor fibre. -/
theorem no_endpointSurvivor_of_certifiedKill {h N L : ℕ}
    (hcert : certifiedKill h N L) :
    ∀ z : ℤ, ¬ endpointSurvivor h N L z := by
  intro z hz
  rcases hcert with ⟨hlow, hhigh⟩
  rcases hz with ⟨hzabs, hzmod⟩
  set B : ℤ := N + h + L + 2
  set P : ℤ := 2 ^ L
  set A : ℤ := windowDiscrepancy h N L
  set r : ℤ := A % P
  have hPpos : 0 < P := by simp [P]
  have hzdecomp : P * (z / P) + r = z := by
    have hzmod' : z % P = A % P := by simpa [r] using hzmod
    change P * (z / P) + A % P = z
    rw [← hzmod']
    exact Int.mul_ediv_add_emod z P
  have hzbox := abs_le.mp hzabs
  by_cases hq : 0 ≤ z / P
  · have hnonneg : 0 ≤ P * (z / P) := mul_nonneg hPpos.le hq
    change B < r at hlow
    linarith
  · have hqneg : z / P ≤ -1 := by omega
    have hmultiple : P * (z / P) ≤ -P := by nlinarith
    change r < P - B at hhigh
    linarith

/-- Under the natural dyadic-room condition, fibre emptiness is not merely a
consequence of `certifiedKill`: it is exactly the central-arc certificate. -/
theorem certifiedKill_of_no_endpointSurvivor {h N L : ℕ}
    (hroom : (2 * (N + h + L + 2) : ℤ) < 2 ^ L)
    (hempty : ∀ z : ℤ, ¬ endpointSurvivor h N L z) :
    certifiedKill h N L := by
  set B : ℤ := N + h + L + 2
  set P : ℤ := 2 ^ L
  set A : ℤ := windowDiscrepancy h N L
  set r : ℤ := A % P
  have hPpos : 0 < P := by simp [P]
  have hr0 : 0 ≤ r := by
    exact Int.emod_nonneg A hPpos.ne'
  have hrP : r < P := Int.emod_lt_of_pos A hPpos
  have hBP : B < P := by
    change 2 * B < P at hroom
    have hB0 : 0 ≤ B := by positivity
    linarith
  unfold certifiedKill
  change B < r ∧ r < P - B
  constructor
  · by_contra h
    have hrB : r ≤ B := le_of_not_gt h
    apply hempty r
    constructor
    · rw [abs_of_nonneg hr0]
      exact hrB
    · change r % P = r
      exact Int.emod_eq_of_lt hr0 hrP
  · by_contra h
    have hrlo : P - B ≤ r := le_of_not_gt h
    apply hempty (r - P)
    constructor
    · have hz0 : r - P ≤ 0 := by linarith
      rw [abs_of_nonpos hz0]
      linarith
    · change (r - P) % P = r
      rw [show r - P = r + P * (-1) by ring,
        Int.add_mul_emod_self_left, Int.emod_eq_of_lt hr0 hrP]

/-- Paper-facing form of the survivor-kernel bridge: once the depth floor is
available, `certifiedKill` is equivalent to exact emptiness of the signed
endpoint fibre. -/
theorem certifiedKill_iff_endpointSurvivor_empty {h N L : ℕ}
    (hroom : (2 * (N + h + L + 2) : ℤ) < 2 ^ L) :
    certifiedKill h N L ↔ ∀ z : ℤ, ¬ endpointSurvivor h N L z :=
  ⟨no_endpointSurvivor_of_certifiedKill,
    certifiedKill_of_no_endpointSurvivor hroom⟩

/-- The tail difference obeys the exact carry recurrence
`D_h(M+1) = 2·D_h(M) - a_{M+1}`. -/
lemma tail_diff_succ (h M : ℕ) :
    totientTail (M + 1 + h) - totientTail (M + 1)
      = 2 * (totientTail (M + h) - totientTail M) - (deltaTotient h (M + 1) : ℝ) := by
  have e1 := totientTail_succ (M + h)
  have e2 := totientTail_succ M
  rw [show M + 1 + h = M + h + 1 from by omega, e1, e2]
  unfold deltaTotient
  push_cast
  rw [show M + 1 + h = M + h + 1 from by omega]
  ring

/-- **Exact endpoint telescoping for every tail difference.**  The first `L`
dyadic digits are the signed increment prefix, and the only remainder is the
translated tail difference scaled by `2⁻ᴸ`.  On the LCM diagonal this is the
dyadic-cocycle collapse: sliding a suffix exposes no independent arithmetic
sample beyond the original carry orbit. -/
lemma tail_diff_eq_increment_prefix_add_shifted (h N L : ℕ) :
    totientTail (N + h) - totientTail N
      = (∑ j ∈ Finset.range L,
          (deltaTotient h (N + 1 + j) : ℝ) / 2 ^ (j + 1))
        + (totientTail (N + L + h) - totientTail (N + L)) / 2 ^ L := by
  rw [totientTail_eq_partial_add_shifted (N + h) L,
    totientTail_eq_partial_add_shifted N L]
  rw [show
      (∑ j ∈ Finset.range L,
          (Nat.totient (N + h + 1 + j) : ℝ) / 2 ^ (j + 1))
          + totientTail (N + h + L) / 2 ^ L
          - ((∑ j ∈ Finset.range L,
              (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1))
            + totientTail (N + L) / 2 ^ L)
        = ((∑ j ∈ Finset.range L,
              (Nat.totient (N + h + 1 + j) : ℝ) / 2 ^ (j + 1))
            - ∑ j ∈ Finset.range L,
              (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1))
          + (totientTail (N + h + L) - totientTail (N + L)) / 2 ^ L by ring,
    ← Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold deltaTotient
    push_cast
    rw [show N + h + 1 + j = N + 1 + j + h by omega]
    ring
  · rw [show N + h + L = N + L + h by omega]

/-! ## The integer carry orbit and the survivor certificate -/

/-- The integer carry orbit launched from candidate `d` at position `N`:
`orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`.  If `D_h(N)` is the
integer `d`, this orbit equals `D_h(N+i)` forever. -/
def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)

/-- **Orbit tracking.**  If the tail difference at `N` is the integer `d`, the
carry orbit computes the exact tail-difference sequence: `orbit i = D_h(N+i)`. -/
lemma carryOrbit_eq_tail_diff {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N d i : ℝ) = totientTail (N + i + h) - totientTail (N + i) := by
  induction i with
  | zero => simpa using hd
  | succ i ih =>
      have hrec := tail_diff_succ h (N + i)
      have hstep : carryOrbit h N d (i + 1)
          = 2 * carryOrbit h N d i - deltaTotient h (N + i + 1) := rfl
      rw [hstep]
      push_cast
      rw [ih, show N + (i + 1) + h = N + i + 1 + h from by omega,
        show N + (i + 1) = N + i + 1 from by omega, hrec]

/-- The **carry-survivor certificate**: every integer candidate in the initial
box `|d| ≤ N+h+1` — enumerated as `d = j - (N+h+1)` for `j < 2·(N+h+1)+1` —
provably escapes the strip `|·| ≤ N+i+h+1` within `K` steps (escape stated as
a two-sided disjunction).  Finitely many candidates, finitely many steps:
decidable. -/
def survivorKill (h N K : ℕ) : Prop :=
  ∀ j ∈ Finset.range (2 * (N + h + 1) + 1),
    ∃ i ∈ Finset.range (K + 1),
      carryOrbit h N ((j : ℤ) - (N + h + 1)) i ≤ -(N + i + h + 2 : ℤ)
        ∨ (N + i + h + 2 : ℤ) ≤ carryOrbit h N ((j : ℤ) - (N + h + 1)) i

instance (h N K : ℕ) : Decidable (survivorKill h N K) := by
  unfold survivorKill
  infer_instance

/-- **Survivor soundness.**  A survivor kill proves the tail difference is not
an integer: an integer value `d` would launch an integer carry orbit equal to
the true tail-difference sequence, which stays inside the strip
`|D_h(N+i)| < N+i+h+2` forever — but the certificate says every candidate
provably escapes within `K` steps.  This is the machine-checked form of the
wave-21 bounded-orbit reformulation. -/
theorem tail_diff_notMem_int_of_survivorKill {h N K : ℕ} (hkill : survivorKill h N K) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨d, hd⟩
  have hboxR : |(d : ℝ)| < (N : ℝ) + h + 2 := by
    rw [hd]
    exact abs_tail_diff_lt h N
  have habs : |d| < (N : ℤ) + h + 2 := by exact_mod_cast hboxR
  have hlohi := abs_lt.mp habs
  have hmem : (d + ((N : ℤ) + h + 1)).toNat ∈ Finset.range (2 * (N + h + 1) + 1) := by
    rw [Finset.mem_range]
    omega
  obtain ⟨i, _, hesc⟩ := hkill (d + ((N : ℤ) + h + 1)).toNat hmem
  have hcand : (((d + ((N : ℤ) + h + 1)).toNat : ℤ)) - ((N : ℤ) + h + 1) = d := by omega
  rw [hcand] at hesc
  have htrack := carryOrbit_eq_tail_diff hd i
  have hstrip := abs_tail_diff_lt h (N + i)
  push_cast at hstrip
  rw [abs_lt] at hstrip
  rcases hesc with hlo | hhi
  · have hR : (carryOrbit h N d i : ℝ) ≤ -((N : ℝ) + i + h + 2) := by exact_mod_cast hlo
    rw [htrack] at hR
    linarith [hstrip.1]
  · have hR : ((N : ℝ) + i + h + 2) ≤ (carryOrbit h N d i : ℝ) := by exact_mod_cast hhi
    rw [htrack] at hR
    linarith [hstrip.2]

/-! ## The multiple-period collapse -/

/-- **Period-ray telescoping.**  The `m·h` tail difference is the sum of `m`
translated `h` tail differences: integrality flows down every multiple. -/
lemma tail_diff_mul (h N m : ℕ) :
    totientTail (N + m * h) - totientTail N
      = ∑ i ∈ Finset.range m,
          (totientTail (N + i * h + h) - totientTail (N + i * h)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih,
        show N + (m + 1) * h = N + m * h + h from by rw [Nat.succ_mul]; omega]
      ring

/-- Integrality propagates down every period ray: if every `h`-difference from
`N₀` on is an integer, so is every `m·h`-difference. -/
lemma tail_diff_mul_mem_int {h N₀ : ℕ}
    (hint : ∀ N, N₀ ≤ N → totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ))
    (m N : ℕ) (hN : N₀ ≤ N) :
    totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := hint (N + m * h) (hN.trans (Nat.le_add_right _ _))
      refine ⟨b + a, ?_⟩
      rw [show N + (m + 1) * h = N + m * h + h from by rw [Nat.succ_mul]; omega]
      push_cast
      rw [ha, hb]
      ring

/-- **The wave-22 reduction: multiple-period survivor supply.**  The weakest
supply hypothesis in the ladder so far: for every primitive period `h₀` it
suffices to certify a survivor kill along ANY multiple `m·h₀`, at arbitrarily
large `N`.  Rationality forces integrality along the whole period ray, so one
dead multiple kills the primitive. -/
theorem irrational_totient_series_of_multiple_survivor_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (m * h₀) N K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨m, _, N, hN, K, hkill⟩ := hsupply h hpos N₀
  exact tail_diff_notMem_int_of_survivorKill hkill (tail_diff_mul_mem_int hint m N hN)

/-- The endpoint-certificate variant of the multiple-period reduction: one
certified window kill along any multiple of each primitive period suffices. -/
theorem irrational_totient_series_of_multiple_certificate_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨h, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  obtain ⟨m, _, N, hN, L, hkill⟩ := hsupply h hpos N₀
  exact tail_diff_notMem_int_of_certifiedKill hkill (tail_diff_mul_mem_int hint m N hN)

/-! ## The one-parameter collapse: `lcm(1..t)` is a universal period ray -/

/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`.  Every
primitive period `h₀ ≤ t` divides it. -/
def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

lemma periodLcm_pos (t : ℕ) : 0 < periodLcm t := by
  induction t with
  | zero => exact Nat.one_pos
  | succ t ih =>
      exact Nat.pos_of_ne_zero (Nat.lcm_ne_zero ih.ne' (Nat.succ_ne_zero t))

lemma dvd_periodLcm {h t : ℕ} (h1 : 1 ≤ h) (ht : h ≤ t) : h ∣ periodLcm t := by
  induction t with
  | zero => omega
  | succ t ih =>
      show h ∣ Nat.lcm (periodLcm t) (t + 1)
      rcases Nat.lt_or_ge h (t + 1) with hlt | hge
      · exact dvd_trans (ih (by omega)) (Nat.dvd_lcm_left _ _)
      · have heq : h = t + 1 := by omega
        subst heq
        exact Nat.dvd_lcm_right _ _

/-- **One-parameter collapse of the throat.**  Survivor kills along the single
family `lcm(1..t)` — arbitrarily large `t`, arbitrarily large `N` — prove #249.
Rationality would give SOME period `h₀`; every `h₀ ≤ t` divides `lcm(1..t)`,
so the whole `∀ h₀` obligation lands on one ℕ-indexed ray. -/
theorem irrational_totient_series_of_lcm_survivor_supply
    (hsupply : ∀ t₀ N₀ : ℕ,
      ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (periodLcm t) N K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_multiple_survivor_supply fun h₀ hpos N₀ => ?_
  obtain ⟨t, ht, N, hN, K, hkill⟩ := hsupply h₀ N₀
  have hdvd : h₀ ∣ periodLcm t := dvd_periodLcm hpos ht
  refine ⟨periodLcm t / h₀,
    Nat.div_pos (Nat.le_of_dvd (periodLcm_pos t) hdvd) hpos, N, hN, K, ?_⟩
  rwa [Nat.div_mul_cancel hdvd]

/-! ## Unconditional deposits (kernel-decided) -/

/-- Machine-checked survivor kill: period `1` dies at `N = 12` within `K = 7`
steps — every integer candidate in `|d| ≤ 14` escapes the strip. -/
theorem survivorKill_example : survivorKill 1 12 7 := by decide

/-- Period `1` has no integer tail difference at `N = 12` — re-derived through
the orbit certificate rather than the endpoint residue. -/
theorem tail_diff_not_int_survivor_example :
    totientTail (12 + 1) - totientTail 12 ∉ Set.range ((↑) : ℤ → ℝ) :=
  tail_diff_notMem_int_of_survivorKill survivorKill_example

/-- The survivor certificate is STRICTLY stronger than the endpoint certificate
at equal depth budget: at `(h, N) = (1, 57)` the survivor interval dies at
`K = 8` while every endpoint window `L ≤ 8` fails.  (The wave-22 probe measures
the two families as near-equivalent in minimal kill depth — this witness pins
down exactly the strictness that remains.) -/
theorem survivor_strict_at_equal_budget :
    survivorKill 1 57 8 ∧ ∀ L ∈ Finset.Icc 1 8, ¬ certifiedKill 1 57 L := by decide

/-- Extended endpoint deposit: every period `h ≤ 16` is certified dead at
`(N, L) = (14, 9)` — twice the wave-21 period range in a smaller window than
its `(12, 16)`. -/
theorem certifiedKill_all_upto_sixteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9 := by decide

/-- No shifted tail difference with period `h ≤ 16` is an integer at `N = 14`. -/
theorem tail_diff_not_int_upto_sixteen (h : ℕ) (h1 : 1 ≤ h) (h16 : h ≤ 16) :
    totientTail (14 + h) - totientTail 14 ∉ Set.range ((↑) : ℤ → ℝ) :=
  tail_diff_notMem_int_of_certifiedKill
    (certifiedKill_all_upto_sixteen h (Finset.mem_Icc.mpr ⟨h1, h16⟩))

/-- **Extended denominator exclusion.**  The totient series equals no rational
whose denominator divides `2¹⁴·(2ʰ-1)` for some `1 ≤ h ≤ 16`: no dyadic
rational with denominator up to `2¹⁴`, and no odd part whose multiplicative
order of `2` is at most `16`.  Subsumes the wave-21 lattice on both axes. -/
theorem totient_series_ne_rat_of_den_dvd_upto_sixteen (r : ℚ) (h : ℕ)
    (h1 : 1 ≤ h) (h16 : h ≤ 16) (hdvd : (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := fun hS =>
  tail_diff_not_int_upto_sixteen h h1 h16 (tail_diff_int_of_den_dvd r hS h 14 hdvd)

#print axioms totientTail_eq_partial_add_shifted
#print axioms tail_diff_eq_increment_prefix_add_shifted

end TotientTailPeriodKiller
end Erdos249257
