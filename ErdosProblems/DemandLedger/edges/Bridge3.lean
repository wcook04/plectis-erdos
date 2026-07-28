import ErdosProblems.DemandLedger.Basic

/-!
# Bridge set 3: block certificates versus lcm kill routes

Left set (the *digit / block certificate* programme, `CertificateKernel`):

* `G088` — block certificates: `∀ q > 0, ∃ N K L C, K ≤ L ∧ (∀ r ≤ K, 2^r ∣ φ(N+r))
  ∧ middle ≤ C ∧ q·(C + N+L+2) < 2^L`
* `G089` — carry certificates: same with `2^K ∣ ∑_{r≤K} φ(N+r)·2^(K-r)`
* `G090` — low-carry certificates: the residue band form
* `G091` — gap certificates: `∀ q > 0, ∃ N K, (q·V) % 2^K + q·(N+K+2) < 2^K`

Right set (the *tail-period killer* programme, `TotientTailPeriodKiller`):

* `G097` — `∀ t₀, ∃ t ≥ t₀, ∃ L, certifiedKill (H t) (H t) L`
* `G100` — `∀ t₀, ∃ t ≥ t₀, ∃ q m L, 0 < q ∧ certifiedKill (m·H t) (q·H t) L`
* `G103` — `∀ t₀ N₀, ∃ t ≥ t₀, ∃ N ≥ N₀, ∃ L, certifiedKill (H t) N L`
* `G094` — `∀ t₀, ∃ t ≥ t₀, ∃ K, survivorKill (H t) (H t) K`

**Result.**  All sixteen left→right pairs are edges, and — more surprisingly —
all four right→`G091` pairs are edges too, so `G091` is *equivalent* to the
whole `certifiedKill` cluster and to Erdős #249 itself.  The block-certificate
programme and the period-killer programme are linked by the proved implications:
the period-killer statements follow from the first three block demands and are
equivalent to the fourth.  No strict non-implication separating the demands is
proved here.

The mechanism in the left→right direction is that irrationality of `S` makes
*every* window non-integral at once (one integral tail difference with `h > 0`
rearranges into `2^N(2^h-1)·S ∈ ℤ`), and both kill predicates are *complete*:
`certifiedKill` by the corpus theorem `exists_certifiedKill_of_tail_diff_notMem_int`,
`survivorKill` by `b3_exists_survivorKill_of_tail_diff_notMem_int` below, which is
new here — the carry orbit launched from an integer candidate `d` differs from
the true tail-difference sequence by `2^i·(d - D)`, and that gap outgrows the
strip as soon as `2^i·dist(D, ℤ) ≥ 2(N+i+h+2)`.

The mechanism in the `G091` direction is that the gap certificate only has to
*miss* a band of relative width `q(N+K+2)/2^K`, and failing to miss it at every
depth pins `q·S` within `q(K+2)/2^K` of an integer — so `q·S ∈ ℤ`.  Missing a
vanishing target is a consequence of irrationality; hitting one (`G088`–`G090`)
is not, and no reverse edge to those three is claimed.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller

namespace DemandLedger.Bridge3

/-! ## Infrastructure I: irrationality forces every window non-integral -/

/-- If `S = ∑ φ(n)/2ⁿ` is irrational then no tail difference with a positive
window is an integer: by the shift identity `2^N·S = Φ_N + R_N`, a single
integral `R_{N+h} - R_N` rearranges into `2^N(2^h-1)·S ∈ ℤ`. -/
theorem b3_tail_diff_notMem_int_of_irrational {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  rintro ⟨d, hd⟩
  have h1 := two_pow_mul_totient_series_eq (N + h)
  have h2 := two_pow_mul_totient_series_eq N
  have hnat : (2 : ℕ) ^ 1 ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hlt : (1 : ℝ) < (2 : ℝ) ^ h := by
    have hc : ((2 ^ 1 : ℕ) : ℝ) ≤ ((2 ^ h : ℕ) : ℝ) := Nat.cast_le.mpr hnat
    push_cast at hc
    linarith
  have h2N : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have hden : ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1)) ≠ 0 :=
    ne_of_gt (mul_pos h2N (by linarith))
  have hkey : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = ((d + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℝ) := by
    have expand : (2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        = (2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
      rw [pow_add]; ring
    rw [expand, h1, h2]
    push_cast
    linarith
  refine hirr ⟨((d + (totientPrefix (N + h) : ℤ) - (totientPrefix N : ℤ) : ℤ) : ℚ)
      / ((2 : ℚ) ^ N * ((2 : ℚ) ^ h - 1)), ?_⟩
  push_cast
  rw [div_eq_iff hden]
  push_cast at hkey
  linear_combination -hkey

/-- Irrationality supplies a firing endpoint certificate at every cell with a
positive window. -/
theorem b3_exists_certifiedKill_of_irrational {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ L, certifiedKill h N L :=
  exists_certifiedKill_of_tail_diff_notMem_int (b3_tail_diff_notMem_int_of_irrational hh hirr)

/-! ## The four left gaps each imply #249 -/

theorem b3_irrational_of_G088 (h : G088) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G088 at h
  exact Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_block_certificates h

theorem b3_irrational_of_G089 (h : G089) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G089 at h
  exact Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_carry_certificates h

theorem b3_irrational_of_G090 (h : G090) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G090 at h
  exact Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_low_carry_certificates h

theorem b3_irrational_of_G091 (h : G091) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G091 at h
  exact Erdos249257.irrational_tsum_totient_div_pow_two_of_gap_certificate_supply h

/-! ## #249 implies the three `certifiedKill` gaps on the right -/

theorem b3_G097_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G097 := by
  unfold G097
  intro t₀
  exact ⟨t₀, le_rfl, b3_exists_certifiedKill_of_irrational (periodLcm_pos t₀) hirr⟩

theorem b3_G100_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G100 := by
  unfold G100
  intro t₀
  obtain ⟨L, hL⟩ := b3_exists_certifiedKill_of_irrational
    (h := 1 * periodLcm t₀) (N := 1 * periodLcm t₀) (by simpa using periodLcm_pos t₀) hirr
  exact ⟨t₀, le_rfl, 1, 1, L, Nat.one_pos, hL⟩

theorem b3_G103_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G103 := by
  unfold G103
  intro t₀ N₀
  exact ⟨t₀, le_rfl, N₀, le_rfl,
    b3_exists_certifiedKill_of_irrational (periodLcm_pos t₀) hirr⟩

/-! ## Infrastructure II: `survivorKill` completeness

`certifiedKill` is known complete (`exists_certifiedKill_of_tail_diff_notMem_int`).
The orbit certificate `survivorKill` is complete too, and the proof is the reason
the two vocabularies describe the same object: the carry orbit launched from an
integer candidate `d` differs from the true tail-difference sequence by exactly
`2^i·(d - D)`, an error that doubles every step while the true sequence stays in
a strip that only grows linearly. -/

private lemma b3_summable_lin : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
  simpa using summable_pow_mul_geometric_of_norm_lt_one 1
    (r := (1 / 2 : ℝ)) (by rw [Real.norm_eq_abs]; norm_num)

private lemma b3_summable_caff (C : ℝ) :
    Summable (fun j : ℕ => (C + (j : ℝ)) * (1 / 2 : ℝ) ^ j) := by
  have h1 : Summable (fun j : ℕ => C * (1 / 2 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  exact (h1.add b3_summable_lin).congr fun j => by ring

/-- A linear-times-geometric majorant can be pushed below any positive bound. -/
theorem b3_exists_depth_lt (C δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℕ, (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L < δ := by
  have htend := (b3_summable_caff C).tendsto_atTop_zero
  have hev : ∀ᶠ L : ℕ in Filter.atTop, (C + (L : ℝ)) * (1 / 2 : ℝ) ^ L ∈ Set.Iio δ :=
    htend.eventually_mem (Iio_mem_nhds hδ)
  obtain ⟨L, hL⟩ := hev.exists
  exact ⟨L, hL⟩

/-- A real which is not an integer stands at a uniform positive distance from
every integer. -/
theorem b3_exists_dist_int_pos {x : ℝ} (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℤ, δ ≤ |x - (z : ℝ)| := by
  obtain ⟨g, hg⟩ := exists_floor x
  have hgle : (g : ℝ) ≤ x := (hg g).mp le_rfl
  have hglt : x < (g : ℝ) + 1 := by
    by_contra hle
    have hle' : (g : ℝ) + 1 ≤ x := not_lt.mp hle
    have h1 : ((g + 1 : ℤ) : ℝ) ≤ x := by push_cast; linarith
    have h2 : g + 1 ≤ g := (hg (g + 1)).mpr h1
    omega
  have hf0 : 0 < x - (g : ℝ) := by
    rcases eq_or_lt_of_le (show 0 ≤ x - (g : ℝ) by linarith) with heq | hlt
    · exact absurd ⟨g, by linarith⟩ hx
    · exact hlt
  refine ⟨min (x - (g : ℝ)) (1 - (x - (g : ℝ))), lt_min hf0 (by linarith), fun z => ?_⟩
  by_cases hz : z ≤ g
  · have hz' : (z : ℝ) ≤ (g : ℝ) := by exact_mod_cast hz
    have hlow : min (x - (g : ℝ)) (1 - (x - (g : ℝ))) ≤ x - (z : ℝ) :=
      le_trans (min_le_left _ _) (by linarith)
    exact hlow.trans (le_abs_self _)
  · have hz1 : g + 1 ≤ z := Int.lt_iff_add_one_le.mp (not_le.mp hz)
    have hz' : (g : ℝ) + 1 ≤ (z : ℝ) := by exact_mod_cast hz1
    have hup : min (x - (g : ℝ)) (1 - (x - (g : ℝ))) ≤ (z : ℝ) - x :=
      le_trans (min_le_right _ _) (by linarith)
    calc min (x - (g : ℝ)) (1 - (x - (g : ℝ))) ≤ (z : ℝ) - x := hup
      _ ≤ |(z : ℝ) - x| := le_abs_self _
      _ = |x - (z : ℝ)| := abs_sub_comm _ _

/-- **Orbit tracking with an offset.**  For an ARBITRARY integer candidate `d`
the carry orbit equals the true tail-difference sequence plus the doubling error
`2^i·(d - D_h(N))`.  (The corpus lemma `carryOrbit_eq_tail_diff` is the special
case where the error vanishes.) -/
theorem b3_carryOrbit_eq (h N : ℕ) (d : ℤ) (i : ℕ) :
    (carryOrbit h N d i : ℝ)
      = 2 ^ i * ((d : ℝ) - (totientTail (N + h) - totientTail N))
        + (totientTail (N + i + h) - totientTail (N + i)) := by
  induction i with
  | zero => simp [carryOrbit]
  | succ i ih =>
      have hrec := tail_diff_succ h (N + i)
      have hstep : carryOrbit h N d (i + 1)
          = 2 * carryOrbit h N d i - deltaTotient h (N + i + 1) := rfl
      rw [hstep]
      push_cast
      rw [ih, show N + (i + 1) + h = N + i + 1 + h from by omega,
        show N + (i + 1) = N + i + 1 from by omega, hrec]
      ring

/-- Once the doubling error outgrows the strip, every candidate escapes. -/
theorem b3_orbit_escape {h N K : ℕ} {δ : ℝ}
    (hdist : ∀ z : ℤ, δ ≤ |(totientTail (N + h) - totientTail N) - (z : ℝ)|)
    (hroom : 2 * ((N : ℝ) + K + h + 2) < δ * 2 ^ K) (d : ℤ) :
    carryOrbit h N d K ≤ -((N : ℤ) + K + h + 2)
      ∨ ((N : ℤ) + K + h + 2) ≤ carryOrbit h N d K := by
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have hstrip := abs_tail_diff_lt h (N + K)
  push_cast at hstrip
  rw [abs_lt] at hstrip
  have horb := b3_carryOrbit_eq h N d K
  have hgap : δ ≤ |(d : ℝ) - (totientTail (N + h) - totientTail N)| := by
    have hz := hdist d
    rwa [abs_sub_comm] at hz
  rcases le_total 0 ((d : ℝ) - (totientTail (N + h) - totientTail N)) with hpos | hneg
  · right
    have he : δ ≤ (d : ℝ) - (totientTail (N + h) - totientTail N) := by
      rwa [abs_of_nonneg hpos] at hgap
    have hbig : δ * 2 ^ K
        ≤ 2 ^ K * ((d : ℝ) - (totientTail (N + h) - totientTail N)) := by
      nlinarith [h2K, he]
    have hreal : ((N : ℝ) + K + h + 2) ≤ (carryOrbit h N d K : ℝ) := by
      rw [horb]
      linarith [hstrip.1]
    exact_mod_cast hreal
  · left
    have he : δ ≤ -((d : ℝ) - (totientTail (N + h) - totientTail N)) := by
      rwa [abs_of_nonpos hneg] at hgap
    have hbig : 2 ^ K * ((d : ℝ) - (totientTail (N + h) - totientTail N))
        ≤ -(δ * 2 ^ K) := by
      nlinarith [h2K, he]
    have hreal : (carryOrbit h N d K : ℝ) ≤ -((N : ℝ) + K + h + 2) := by
      rw [horb]
      linarith [hstrip.2]
    exact_mod_cast hreal

/-- **Survivor completeness.**  If the tail difference is a non-integer, some
finite step budget certifies it in the orbit vocabulary too.  This is the
`survivorKill` analogue of the corpus theorem
`exists_certifiedKill_of_tail_diff_notMem_int`. -/
theorem b3_exists_survivorKill_of_tail_diff_notMem_int {h N : ℕ}
    (hD : totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ K, survivorKill h N K := by
  obtain ⟨δ, hδ0, hdist⟩ := b3_exists_dist_int_pos hD
  obtain ⟨K, hK⟩ := b3_exists_depth_lt ((N : ℝ) + h + 2) (δ / 2) (by positivity)
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  have hroom : 2 * ((N : ℝ) + K + h + 2) < δ * 2 ^ K := by
    have hrw : ((N : ℝ) + h + 2 + (K : ℝ)) * (1 / 2 : ℝ) ^ K
        = ((N : ℝ) + h + 2 + (K : ℝ)) / 2 ^ K := by
      rw [div_pow, one_pow]
      ring
    rw [hrw, div_lt_iff₀ h2K] at hK
    linarith
  exact ⟨K, fun j _ => ⟨K, Finset.self_mem_range_succ K,
    b3_orbit_escape hdist hroom _⟩⟩

/-- Irrationality supplies a firing survivor certificate at every cell with a
positive window. -/
theorem b3_exists_survivorKill_of_irrational {h N : ℕ} (hh : 0 < h)
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ K, survivorKill h N K :=
  b3_exists_survivorKill_of_tail_diff_notMem_int
    (b3_tail_diff_notMem_int_of_irrational hh hirr)

theorem b3_G094_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G094 := by
  unfold G094
  intro t₀
  exact ⟨t₀, le_rfl, b3_exists_survivorKill_of_irrational (periodLcm_pos t₀) hirr⟩

/-! ## Twelve edges: block certificates ⟹ the `certifiedKill` routes -/

theorem e_G088_G097 : G088 → G097 := fun h => b3_G097_of_irrational (b3_irrational_of_G088 h)
theorem e_G088_G100 : G088 → G100 := fun h => b3_G100_of_irrational (b3_irrational_of_G088 h)
theorem e_G088_G103 : G088 → G103 := fun h => b3_G103_of_irrational (b3_irrational_of_G088 h)

theorem e_G089_G097 : G089 → G097 := fun h => b3_G097_of_irrational (b3_irrational_of_G089 h)
theorem e_G089_G100 : G089 → G100 := fun h => b3_G100_of_irrational (b3_irrational_of_G089 h)
theorem e_G089_G103 : G089 → G103 := fun h => b3_G103_of_irrational (b3_irrational_of_G089 h)

theorem e_G090_G097 : G090 → G097 := fun h => b3_G097_of_irrational (b3_irrational_of_G090 h)
theorem e_G090_G100 : G090 → G100 := fun h => b3_G100_of_irrational (b3_irrational_of_G090 h)
theorem e_G090_G103 : G090 → G103 := fun h => b3_G103_of_irrational (b3_irrational_of_G090 h)

theorem e_G091_G097 : G091 → G097 := fun h => b3_G097_of_irrational (b3_irrational_of_G091 h)
theorem e_G091_G100 : G091 → G100 := fun h => b3_G100_of_irrational (b3_irrational_of_G091 h)
theorem e_G091_G103 : G091 → G103 := fun h => b3_G103_of_irrational (b3_irrational_of_G091 h)

/-! ## Infrastructure III: irrationality supplies gap certificates

The gap certificate does not have to *hit* a small residue band, only to *miss*
the thin top band of width `q·(N+K+2)` out of `2^K`.  Failing to miss it at
depth `K` (with `N = 0`) pins `q·S` within `q(K+2)/2^K` of an integer, so
failing at every depth makes `q·S` an integer outright.  Irrationality therefore
*supplies* the certificate — in sharp contrast to `G088`–`G090`, whose
certificates are hitting conditions and are not claimed to follow from #249. -/

/-- The packed first block over `Icc 1 K`, divided by `2^K`, is the depth-`K`
partial tail at `N = 0`. -/
theorem b3_block_eq (K : ℕ) :
    ((∑ r ∈ Finset.Icc 1 K, Nat.totient (0 + r) * 2 ^ (K - r) : ℕ) : ℝ) / 2 ^ K
      = ∑ j ∈ Finset.range K, (Nat.totient (0 + 1 + j) : ℝ) / 2 ^ (j + 1) := by
  have hreidx : (∑ r ∈ Finset.Icc 1 K, Nat.totient (0 + r) * 2 ^ (K - r))
      = ∑ i ∈ Finset.range K, Nat.totient (0 + 1 + i) * 2 ^ (K - (i + 1)) := by
    have hIccIco : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
      ext a
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIccIco, Finset.sum_Ico_eq_sum_range]
    have hn : K + 1 - 1 = K := by omega
    rw [hn]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : 0 + (1 + i) = 0 + 1 + i := by omega
    have h2 : K - (1 + i) = K - (i + 1) := by omega
    rw [h1, h2]
  rw [hreidx]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiK : i < K := Finset.mem_range.mp hi
  have hsplit : (2 : ℝ) ^ K = (2 : ℝ) ^ (K - (i + 1)) * (2 : ℝ) ^ (i + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  have hne1 : ((2 : ℝ) ^ (K - (i + 1))) ≠ 0 := by positivity
  have hne2 : ((2 : ℝ) ^ (i + 1)) ≠ 0 := by positivity
  field_simp

/-- **The gap certificate fires at `N = 0` as soon as the depth beats the
distance from `q·S` to the integers.** -/
theorem b3_gap_cert_of_dist {q K : ℕ} {δ : ℝ} (hq : 0 < q)
    (hdist : ∀ z : ℤ, δ ≤ |(q : ℝ) * totientTail 0 - (z : ℝ)|)
    (hbig : (q : ℝ) * ((K : ℝ) + 2) < δ * 2 ^ K) :
    (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (0 + r) * 2 ^ (K - r)) % 2 ^ K)) % 2 ^ K
      + q * (0 + K + 2) < 2 ^ K := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  by_contra hcon0
  have hcon := Nat.not_lt.mp hcon0
  set A : ℕ := ∑ r ∈ Finset.Icc 1 K, Nat.totient (0 + r) * 2 ^ (K - r) with hAdef
  have hblock : (A : ℝ) / 2 ^ K
      = ∑ j ∈ Finset.range K, (Nat.totient (0 + 1 + j) : ℝ) / 2 ^ (j + 1) := by
    rw [hAdef]
    exact b3_block_eq K
  have hmodeq : q * (A % 2 ^ K) % 2 ^ K = q * A % 2 ^ K :=
    Nat.ModEq.mul_left q (Nat.mod_modEq A (2 ^ K))
  rw [hmodeq] at hcon
  set W : ℕ := q * A % 2 ^ K with hWdef
  set c : ℕ := q * A / 2 ^ K with hcdef
  have hdm : 2 ^ K * c + W = q * A := Nat.div_add_mod (q * A) (2 ^ K)
  have hWlt : W < 2 ^ K := Nat.mod_lt _ (by positivity)
  have hdmR : (2 : ℝ) ^ K * (c : ℝ) + (W : ℝ) = (q : ℝ) * (A : ℝ) := by exact_mod_cast hdm
  have hWltR : (W : ℝ) < 2 ^ K := by exact_mod_cast hWlt
  have hconR : ((2 : ℝ) ^ K) ≤ (W : ℝ) + (q : ℝ) * ((K : ℝ) + 2) := by
    have h : ((2 ^ K : ℕ) : ℝ) ≤ ((W + q * (0 + K + 2) : ℕ) : ℝ) := Nat.cast_le.mpr hcon
    push_cast at h
    linarith
  obtain ⟨P, T, hsplit, hPeq, hTn, hTK⟩ :
      ∃ P T : ℝ, totientTail 0 = P + T ∧ (A : ℝ) / 2 ^ K = P ∧ 0 ≤ T
        ∧ T * 2 ^ K ≤ (K : ℝ) + 2 := by
    refine ⟨_, _, totientTail_eq_partial_add_tail 0 K, hblock, tail_after_nonneg 0 K, ?_⟩
    have h := mul_le_mul_of_nonneg_right (tail_after_le 0 K) (le_of_lt h2K)
    rw [div_mul_cancel₀ _ h2K.ne'] at h
    push_cast at h
    linarith
  have hqu : (q : ℝ) * ((A : ℝ) / 2 ^ K) = (c : ℝ) + (W : ℝ) / 2 ^ K := by
    have e1 : (q : ℝ) * ((A : ℝ) / 2 ^ K) = ((q : ℝ) * (A : ℝ)) / 2 ^ K := by ring
    rw [e1, ← hdmR, add_div, mul_div_cancel_left₀ (c : ℝ) h2K.ne']
  have hx : (q : ℝ) * totientTail 0 = (c : ℝ) + (W : ℝ) / 2 ^ K + (q : ℝ) * T := by
    rw [hsplit, mul_add, ← hPeq, hqu]
  have hWc : (W : ℝ) / 2 ^ K * 2 ^ K = (W : ℝ) := div_mul_cancel₀ _ h2K.ne'
  have hy : ((q : ℝ) * totientTail 0 - ((c : ℝ) + 1)) * 2 ^ K
      = ((W : ℝ) - 2 ^ K) + (q : ℝ) * (T * 2 ^ K) := by
    linear_combination ((2 : ℝ) ^ K) * hx + hWc
  have hZ0 : 0 ≤ (q : ℝ) * (T * 2 ^ K) :=
    mul_nonneg (le_of_lt hq') (mul_nonneg hTn (le_of_lt h2K))
  have hZu : (q : ℝ) * (T * 2 ^ K) ≤ (q : ℝ) * ((K : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left hTK (le_of_lt hq')
  have habs : |((q : ℝ) * totientTail 0 - ((c : ℝ) + 1)) * 2 ^ K|
      ≤ (q : ℝ) * ((K : ℝ) + 2) := by
    rw [abs_le]
    refine ⟨?_, ?_⟩ <;> rw [hy] <;> linarith
  rw [abs_mul, abs_of_pos h2K] at habs
  have hdc := hdist ((c : ℤ) + 1)
  push_cast at hdc
  have hfin := mul_le_mul_of_nonneg_right hdc (le_of_lt h2K)
  linarith [habs, hbig, hfin]

/-- **#249 implies the gap-certificate supply.**  The gap certificate is a
*miss* condition, and irrationality is exactly what guarantees the miss. -/
theorem b3_G091_of_irrational (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    G091 := by
  unfold G091
  intro q hq
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := hq'.ne'
  have hS0 : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = totientTail 0 := by
    have h := two_pow_mul_totient_series_eq 0
    have hp : totientPrefix 0 = 0 := by decide
    rw [hp] at h
    simpa using h
  have hxnot : (q : ℝ) * totientTail 0 ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨z, hz⟩
    refine hirr ⟨(z : ℚ) / (q : ℚ), ?_⟩
    rw [hS0]
    push_cast
    rw [div_eq_iff hqne]
    linear_combination hz
  obtain ⟨δ, hδ0, hdist⟩ := b3_exists_dist_int_pos hxnot
  obtain ⟨K, hK⟩ := b3_exists_depth_lt 2 (δ / (q : ℝ)) (div_pos hδ0 hq')
  have h2K : (0 : ℝ) < 2 ^ K := by positivity
  refine ⟨0, K, b3_gap_cert_of_dist hq hdist ?_⟩
  have hstep : ((2 + (K : ℝ)) * (1 / 2 : ℝ) ^ K) * ((q : ℝ) * 2 ^ K)
      < (δ / (q : ℝ)) * ((q : ℝ) * 2 ^ K) :=
    mul_lt_mul_of_pos_right hK (by positivity)
  have hpow : ((1 : ℝ) / 2) ^ K * 2 ^ K = 1 := by
    rw [← mul_pow]
    norm_num
  have e1 : ((2 + (K : ℝ)) * (1 / 2 : ℝ) ^ K) * ((q : ℝ) * 2 ^ K)
      = (q : ℝ) * ((K : ℝ) + 2) := by
    calc ((2 + (K : ℝ)) * (1 / 2 : ℝ) ^ K) * ((q : ℝ) * 2 ^ K)
        = (q : ℝ) * ((2 + (K : ℝ)) * ((1 / 2 : ℝ) ^ K * 2 ^ K)) := by ring
      _ = (q : ℝ) * ((K : ℝ) + 2) := by rw [hpow]; ring
  have e2 : (δ / (q : ℝ)) * ((q : ℝ) * 2 ^ K) = δ * 2 ^ K := by
    field_simp
  rw [e1, e2] at hstep
  exact hstep

/-! ## Four more edges: block certificates ⟹ the `survivorKill` route -/

theorem e_G088_G094 : G088 → G094 := fun h => b3_G094_of_irrational (b3_irrational_of_G088 h)
theorem e_G089_G094 : G089 → G094 := fun h => b3_G094_of_irrational (b3_irrational_of_G089 h)
theorem e_G090_G094 : G090 → G094 := fun h => b3_G094_of_irrational (b3_irrational_of_G090 h)
theorem e_G091_G094 : G091 → G094 := fun h => b3_G094_of_irrational (b3_irrational_of_G091 h)

/-! ## The four right gaps each imply #249 (the corpus supply theorems) -/

theorem b3_irrational_of_G097 (h : G097) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G097 at h
  exact irrational_totient_series_of_lcm_diagonal_certificate_supply h

theorem b3_irrational_of_G100 (h : G100) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G100 at h
  exact Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply h

theorem b3_irrational_of_G103 (h : G103) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G103 at h
  exact Erdos249257.irrational_totient_series_of_lcm_window_kill_supply h

theorem b3_irrational_of_G094 (h : G094) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  unfold G094 at h
  exact irrational_totient_series_of_lcm_diagonal_survivor_supply h

/-! ## Four backward edges: the kill routes ⟹ the gap-certificate supply -/

theorem e_G097_G091 : G097 → G091 := fun h => b3_G091_of_irrational (b3_irrational_of_G097 h)
theorem e_G100_G091 : G100 → G091 := fun h => b3_G091_of_irrational (b3_irrational_of_G100 h)
theorem e_G103_G091 : G103 → G091 := fun h => b3_G091_of_irrational (b3_irrational_of_G103 h)
theorem e_G094_G091 : G094 → G091 := fun h => b3_G091_of_irrational (b3_irrational_of_G094 h)

/-! ## The collapse

`G091` is not a separate frontier record: it is Erdős #249, and so are all four
gaps on the right.  Only `G088`, `G089`, `G090` — the three *hitting* conditions
— remain strictly stronger demands (no reverse edge to them is claimed here). -/

theorem b3_G091_iff_G097 : G091 ↔ G097 := ⟨e_G091_G097, e_G097_G091⟩
theorem b3_G091_iff_G100 : G091 ↔ G100 := ⟨e_G091_G100, e_G100_G091⟩
theorem b3_G091_iff_G103 : G091 ↔ G103 := ⟨e_G091_G103, e_G103_G091⟩
theorem b3_G091_iff_G094 : G091 ↔ G094 := ⟨e_G091_G094, e_G094_G091⟩

theorem b3_G091_iff_erdos249 :
    G091 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨b3_irrational_of_G091, b3_G091_of_irrational⟩

theorem b3_G094_iff_erdos249 :
    G094 ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  ⟨b3_irrational_of_G094, b3_G094_of_irrational⟩

end DemandLedger.Bridge3
