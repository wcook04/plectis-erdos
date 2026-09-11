import Erdos249257.LcmConeFlatness

/-!
# Wave 25: the cone non-flatness refuter — killing the menu, not the pair

Wave 24 proved that rationality forces ONE fractional constant on the whole
lcm cone `{k·H_t : k ≥ 1}`.  Every certificate so far interrogates that
constant through a single PAIR of cone points.  This file interrogates a
whole finite MENU `Q = [q₁, …, q_k]` of cone vertices at once.

**The refuter.**  At depth `L` each vertex `q·H` pins the real point
`2^L·R_{q·H}` inside the one-sided arc

  `[P_L(q·H), P_L(q·H) + (q·H + L + 2)]  (mod 2^L)`,

where `P_L` is the integer window numerator (`windowNumerator`) and the
radius is the one-sided deep-tail bound.  If ALL the vertices share one
fractional part — cone flatness — those arcs must share a common point.
`coneNonflatCert` is the decidable statement that every arc's LEFT ENDPOINT
escapes some arc of the menu; by an argmin argument this refutes ANY common
point, hence refutes joint flatness outright
(`exists_nonintegral_pair_of_coneNonflatCert`): some pair of menu vertices
has a non-integral tail difference.  No circle topology, no Helly: if a
common point existed, the vertex of MINIMAL deep tail would be a common
left endpoint, and the certificate row at that vertex is exactly its
denial.

**Why this is sharper than pairwise kills.**  `certifiedKill` charges the
two-sided band `±(N+h+L+2)` — the TOP vertex's radius on BOTH sides.  The
menu refuter charges each arc only its OWN one-sided radius, so its
information floor `2^L > max_q(q·H+L+2)` is HALF the pairwise floor, and
even a 2-menu can fire strictly below every pairwise kill of the same menu.
For `|Q| ≥ 3` the refutation is genuinely joint: the menu can be
inconsistent while every pair alone stays consistent (empty common
intersection without any empty pairwise intersection).  Probe v3 measures
the strict-win census; the kernel-checked fixtures below deposit the first
firing cells.

**Supply.**  One firing menu (positive vertices, one-sided floors) at
arbitrarily large scale proves #249
(`irrational_totient_series_of_lcm_cone_nonflat_supply`).  The lcm-jump
lane is also named once and for all: certified kills at
`(h, N) = (H_{t+1} - H_t, H_t)` at arbitrarily large `t` prove #249
(`irrational_totient_series_of_lcm_jump_kill_supply`) — jumps are the cone
cells `(q, m) = (1, p-1)` and need no side condition at all, because a
`h = 0` window can never be certified.

The supply hypotheses remain the open content of #249 and are NOT claimed.
Everything is elementary: geometric tails, an argmin over a finite menu,
and integer window arithmetic.
-/

set_option maxRecDepth 100000

namespace Erdos249257
namespace TotientTailPeriodKiller

open Finset

/-! ## Small-prime support of the cone window argument (wave 30)

For every prime `p ≤ t`, `p ∣ periodLcm t`, so `q·periodLcm t + s ≡ s (mod p)`:
the primes `≤ t` dividing the cone window argument `q·H_t + s` are exactly the
primes dividing the offset `s`.  This is the elementary door behind the wave-29
rough identity `φ(qH_t+s) ≈ qH_t·φ(s)/s` and the wave-30 smooth-envelope split
`P_L = E_L − Δ_L` — below `2t` the window totients carry only `s`'s small-prime
structure plus a non-negative fresh-prime (`> t`) defect.  It is NOT a supply
step: it does not fire any certificate, it fixes the arithmetic of the window
argument. -/
theorem small_prime_dvd_cone_window_iff_dvd_offset
    {t q s p : ℕ} (hp : p.Prime) (hpt : p ≤ t) :
    p ∣ q * periodLcm t + s ↔ p ∣ s := by
  have hpq : p ∣ q * periodLcm t := (dvd_periodLcm hp.pos hpt).mul_left q
  exact Nat.dvd_add_right hpq

/-! ## The window numerator and its one-sided tail band -/

/-- The depth-`L` window numerator `P_L(M) = Σ_{j<L} φ(M+1+j)·2^{L-1-j}`:
the integer layer of `2^L·R_M`, exact up to the one-sided deep tail
`0 ≤ 2^L·R_M - P_L(M) ≤ M+L+2`. -/
def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)

/-- The window numerator over `2^L` is the depth-`L` partial tail. -/
lemma windowNumerator_div_eq (M L : ℕ) :
    ((windowNumerator M L : ℕ) : ℝ) / 2 ^ L
      = ∑ j ∈ Finset.range L, (Nat.totient (M + 1 + j) : ℝ) / 2 ^ (j + 1) := by
  unfold windowNumerator
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL : j < L := Finset.mem_range.mp hj
  have hsplit : (2 : ℝ) ^ L = 2 ^ (L - 1 - j) * 2 ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : (2 : ℝ) ^ (j + 1) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ (L - 1 - j) ≠ 0 := by positivity
  rw [hsplit]
  field_simp

/-! ## The menu refuter -/

/-- **The cone non-flatness certificate.**  For the vertex menu `Q` at scale
`H` and depth `L`: every left endpoint `P_L(qᵢ·H)` escapes some arc
`[P_L(qⱼ·H), P_L(qⱼ·H) + (qⱼ·H+L+2)]` modulo `2^L`.  A `|Q|²` one-sided
window check; decidable. -/
def coneNonflatCert (H L : ℕ) (Q : List ℕ) : Prop :=
  ∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((windowNumerator (qi * H) L : ℤ) - (windowNumerator (qj * H) L : ℤ)) % 2 ^ L

instance (H L : ℕ) (Q : List ℕ) : Decidable (coneNonflatCert H L Q) :=
  inferInstanceAs (Decidable (∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((windowNumerator (qi * H) L : ℤ) - (windowNumerator (qj * H) L : ℤ)) % 2 ^ L))

/-- **Menu refutation soundness.**  If the certificate fires and the
one-sided floor `2^L > q·H+L+2` holds at every vertex, then some pair of
menu vertices has a NON-integral tail difference.  Proof shape: were every
pair integral, the vertex `q⋆` of minimal deep tail would give, for every
menu vertex `q`, the integer `C = P(q⋆·H) - P(q·H) + k·2^L` equal to the
real number `(T_q - T_{q⋆})·2^L ∈ [0, q·H+L+2]` — so the left endpoint
`P(q⋆·H)` sits inside EVERY arc, and the certificate row at `q⋆` is exactly
the denial of that. -/
theorem exists_nonintegral_pair_of_coneNonflatCert {H L : ℕ} {Q : List ℕ}
    (hQ : Q ≠ [])
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : coneNonflatCert H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  by_contra hall
  push Not at hall
  -- the vertex of minimal deep tail at depth L
  obtain ⟨x, hxQ⟩ := List.exists_mem_of_ne_nil Q hQ
  have hne : Q.toFinset.Nonempty := ⟨x, List.mem_toFinset.mpr hxQ⟩
  obtain ⟨qs, hqsF, hmin⟩ := Q.toFinset.exists_min_image
    (fun q => ∑' j : ℕ, (Nat.totient (q * H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)) hne
  have hqsQ : qs ∈ Q := List.mem_toFinset.mp hqsF
  -- its certificate row and the assumed integrality across that pair
  obtain ⟨qj, hqjQ, hrow⟩ := hcert qs hqsQ
  obtain ⟨k, hk⟩ := hall qs hqsQ qj hqjQ
  have hminj : (∑' j : ℕ, (Nat.totient (qs * H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1))
      ≤ ∑' j : ℕ, (Nat.totient (qj * H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) :=
    hmin qj (List.mem_toFinset.mpr hqjQ)
  -- window decompositions at depth L
  have hdecs := totientTail_eq_partial_add_tail (qs * H) L
  have hdecj := totientTail_eq_partial_add_tail (qj * H) L
  have hWs := windowNumerator_div_eq (qs * H) L
  have hWj := windowNumerator_div_eq (qj * H) L
  have hTs0 := tail_after_nonneg (qs * H) L
  have hTj0 := tail_after_nonneg (qj * H) L
  have hTju := tail_after_le (qj * H) L
  push_cast at hTju
  set Ws := windowNumerator (qs * H) L with hWsdef
  set Wj := windowNumerator (qj * H) L with hWjdef
  set Ts := ∑' j : ℕ, (Nat.totient (qs * H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
    with hTsdef
  set Tj := ∑' j : ℕ, (Nat.totient (qj * H + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1)
    with hTjdef
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  -- fold the two vertex decompositions into hk
  rw [hdecj, hdecs, ← hWj, ← hWs] at hk
  -- the bridging integer C = (Ws - Wj) + k·2^L equals (Tj - Ts)·2^L ∈ [0, qj·H+L+2]
  set C : ℤ := (Ws : ℤ) - (Wj : ℤ) + k * 2 ^ L with hCdef
  have hCreal : (C : ℝ) = (Tj - Ts) * 2 ^ L := by
    have e1 : (((Wj : ℝ) / 2 ^ L + Tj) - ((Ws : ℝ) / 2 ^ L + Ts)) * 2 ^ L
        = (Wj : ℝ) - (Ws : ℝ) + (Tj - Ts) * 2 ^ L := by
      rw [sub_mul, add_mul, add_mul, div_mul_cancel₀ _ h2L.ne', div_mul_cancel₀ _ h2L.ne']
      ring
    have e2 : ((k : ℤ) : ℝ) * 2 ^ L = (Wj : ℝ) - (Ws : ℝ) + (Tj - Ts) * 2 ^ L := by
      rw [hk, e1]
    rw [hCdef]
    push_cast
    linarith [e2]
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := by
    rw [hCreal]
    exact mul_nonneg (by linarith [hminj]) h2L.le
  have hCub : (C : ℝ) ≤ (qj : ℝ) * H + L + 2 := by
    rw [hCreal]
    have hTj2L : Tj * 2 ^ L ≤ (qj : ℝ) * H + L + 2 := by
      have h' := mul_le_mul_of_nonneg_right hTju h2L.le
      rw [div_mul_cancel₀ _ h2L.ne'] at h'
      linarith [h']
    have hstep : (Tj - Ts) * 2 ^ L ≤ Tj * 2 ^ L :=
      mul_le_mul_of_nonneg_right (by linarith [hTs0]) h2L.le
    linarith
  have hC0 : (0 : ℤ) ≤ C := by exact_mod_cast hCnn
  have hCle : C ≤ (qj * H + L + 2 : ℤ) := by exact_mod_cast hCub
  -- C and Ws - Wj agree modulo 2^L, and C is already reduced
  have hemod : C % 2 ^ L = ((Ws : ℤ) - (Wj : ℤ)) % 2 ^ L := by
    rw [hCdef,
      show (Ws : ℤ) - (Wj : ℤ) + k * 2 ^ L = (Ws : ℤ) - (Wj : ℤ) + 2 ^ L * k from by ring,
      Int.add_mul_emod_self_left]
  have hCid : C % 2 ^ L = C :=
    Int.emod_eq_of_lt hC0 (lt_of_le_of_lt hCle (hfloor qj hqjQ))
  -- the certificate row at q⋆ denies exactly this membership
  rw [← hemod, hCid] at hrow
  exact absurd hrow (not_lt.mpr hCle)

/-! ## Supply: one firing menu at arbitrarily large scale proves #249 -/

/-- **The cone non-flatness supply theorem.**  If for arbitrarily large `t`
some finite positive vertex menu on the `lcm(1..t)` cone fires the
non-flatness certificate (with its one-sided floors), the totient series is
irrational.  Rationality flattens the cone — every pair of menu vertices
would have integral difference — and the refuter denies all of them at
once. -/
theorem irrational_totient_series_of_lcm_cone_nonflat_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : List ℕ, Q ≠ [] ∧
      (∀ q ∈ Q, 0 < q) ∧ (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      coneNonflatCert (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  by_contra hrat
  obtain ⟨t₁, hflat⟩ := rational_totient_series_forces_lcm_cone_flatness hrat
  obtain ⟨t, ht, L, Q, hQne, hQpos, hfloor, hcert⟩ := hsupply t₁
  obtain ⟨qi, hqi, qj, hqj, hnon⟩ :=
    exists_nonintegral_pair_of_coneNonflatCert hQne hfloor hcert
  refine hnon ?_
  rcases Nat.le_total qi qj with hle | hle
  · have hmem := hflat t ht qi (qj - qi) (hQpos qi hqi)
    rwa [show qi * periodLcm t + (qj - qi) * periodLcm t = qj * periodLcm t from by
      rw [← Nat.add_mul]
      congr 1
      omega] at hmem
  · have hmem := hflat t ht qj (qi - qj) (hQpos qj hqj)
    rw [show qj * periodLcm t + (qi - qj) * periodLcm t = qi * periodLcm t from by
      rw [← Nat.add_mul]
      congr 1
      omega] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact ⟨-a, by push_cast; linarith [ha]⟩

/-! ## The lcm-jump lane, named once and for all -/

/-- **Jump supply.**  Certified kills at the lcm jumps —
`(h, N) = (H_{t+1} - H_t, H_t)` at arbitrarily large `t` — prove #249.
Each jump is the cone cell `(q, m) = (1, H_{t+1}/H_t - 1)`; no side
condition is needed because `H_t ∣ H_{t+1}` makes the multiplier exact
(and a `h = 0` window can never be certified). -/
theorem irrational_totient_series_of_lcm_jump_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      certifiedKill (periodLcm (t + 1) - periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  refine irrational_totient_series_of_lcm_cone_certificate_supply fun t₀ => ?_
  obtain ⟨t, ht, L, hkill⟩ := hsupply t₀
  refine ⟨t, ht, 1, periodLcm (t + 1) / periodLcm t - 1, L, one_pos, ?_⟩
  have hdvd : periodLcm t ∣ periodLcm (t + 1) := periodLcm_dvd_periodLcm (Nat.le_succ t)
  have hm : (periodLcm (t + 1) / periodLcm t - 1) * periodLcm t
      = periodLcm (t + 1) - periodLcm t := by
    rw [Nat.sub_mul, Nat.div_mul_cancel hdvd, one_mul]
  rw [one_mul, hm]
  exact hkill

/-! ## Exactness and depth-monotonicity of the menu refuter

Wave 27.  The probe's argmin characterisation — certificate fires iff NO
common point exists — and the depth law behind `nonflat_L_min` become
kernel facts.  Three moving parts, all elementary: a purely combinatorial
argmin (no analytic tails), the window recursion
`P_{L+1}(M) = 2·P_L(M) + φ(M+L+1)`, and a halving descent for common
points.  Consequences: the certificate is monotone in depth (fires at `L`
⟹ fires at every `L' ≥ L` with floors held), so `∃L` in any supply
statement collapses onto canonical large-enough depths, and the probe's
`nonflat_L_min` acquires kernel meaning as THE firing threshold. -/

/-- A **common point** of the depth-`L` menu arcs: an integer residue whose
one-sided distance from every left endpoint `P_L(q·H)` stays inside that
vertex's arc radius `q·H+L+2` modulo `2^L`.  Joint flatness of the menu
would pin `2^L·μ` at exactly such a point. -/
def coneCommonPoint (H L : ℕ) (Q : List ℕ) : Prop :=
  ∃ y : ℤ, ∀ q ∈ Q,
    (y - (windowNumerator (q * H) L : ℤ)) % 2 ^ L ≤ q * H + L + 2

/-- The window recursion: one more depth bit appends one totient value,
`P_{L+1}(M) = 2·P_L(M) + φ(M+L+1)`. -/
lemma windowNumerator_succ (M L : ℕ) :
    windowNumerator M (L + 1)
      = 2 * windowNumerator M L + Nat.totient (M + 1 + L) := by
  unfold windowNumerator
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hlast : L + 1 - 1 - L = 0 := by omega
  rw [hlast, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL : j < L := Finset.mem_range.mp hj
  have hexp : L + 1 - 1 - j = (L - 1 - j) + 1 := by omega
  rw [hexp, pow_succ]
  ring

/-- **Refuter soundness against common points**: a firing certificate
denies every common point — the combinatorial argmin.  If `y` were common,
the vertex `q⋆` of minimal one-sided distance to `y` would have its left
endpoint inside EVERY arc, and `q⋆`'s certificate row denies exactly
that. -/
theorem not_coneCommonPoint_of_coneNonflatCert {H L : ℕ} {Q : List ℕ}
    (hQ : Q ≠ []) (hcert : coneNonflatCert H L Q) :
    ¬ coneCommonPoint H L Q := by
  rintro ⟨y, hy⟩
  have h2L : (0 : ℤ) < 2 ^ L := by positivity
  obtain ⟨x, hxQ⟩ := List.exists_mem_of_ne_nil Q hQ
  have hne : Q.toFinset.Nonempty := ⟨x, List.mem_toFinset.mpr hxQ⟩
  obtain ⟨qs, hqsF, hmin⟩ := Q.toFinset.exists_min_image
    (fun q => (y - (windowNumerator (q * H) L : ℤ)) % 2 ^ L) hne
  have hqsQ : qs ∈ Q := List.mem_toFinset.mp hqsF
  obtain ⟨qj, hqjQ, hrow⟩ := hcert qs hqsQ
  set as : ℤ := (y - (windowNumerator (qs * H) L : ℤ)) % 2 ^ L with has
  set aj : ℤ := (y - (windowNumerator (qj * H) L : ℤ)) % 2 ^ L with haj
  have hmin' : as ≤ aj := hmin qj (List.mem_toFinset.mpr hqjQ)
  have hasnn : (0 : ℤ) ≤ as := Int.emod_nonneg _ (ne_of_gt h2L)
  have hajlt : aj < 2 ^ L := Int.emod_lt_of_pos _ h2L
  have hdiff : ((windowNumerator (qs * H) L : ℤ)
      - (windowNumerator (qj * H) L : ℤ)) % 2 ^ L = aj - as := by
    have hsplit : (windowNumerator (qs * H) L : ℤ)
        - (windowNumerator (qj * H) L : ℤ)
        = (y - (windowNumerator (qj * H) L : ℤ))
          - (y - (windowNumerator (qs * H) L : ℤ)) := by ring
    rw [hsplit, Int.sub_emod, ← haj, ← has]
    exact Int.emod_eq_of_lt (by linarith) (by linarith)
  rw [hdiff] at hrow
  have hbound := hy qj hqjQ
  rw [← haj] at hbound
  linarith

/-- **Refuter completeness against common points**: if no common point
exists, the certificate fires — a silent row at `qi` would make the left
endpoint `P_L(qi·H)` itself a common point. -/
theorem coneNonflatCert_of_not_coneCommonPoint {H L : ℕ} {Q : List ℕ}
    (h : ¬ coneCommonPoint H L Q) : coneNonflatCert H L Q := by
  intro qi hqi
  by_contra hno
  push Not at hno
  exact h ⟨(windowNumerator (qi * H) L : ℤ), fun q hq => hno q hq⟩

/-- **Exactness of the menu refuter, kernel-checked**: the certificate
fires iff the menu arcs share NO common point.  This is the law the probe
gate `nonflat_matches_common_point_bruteforce` measured at every tested
cell; it is now a theorem at every cell. -/
theorem coneNonflatCert_iff_no_common_point {H L : ℕ} {Q : List ℕ}
    (hQ : Q ≠ []) :
    coneNonflatCert H L Q ↔ ¬ coneCommonPoint H L Q :=
  ⟨not_coneCommonPoint_of_coneNonflatCert hQ,
    coneNonflatCert_of_not_coneCommonPoint⟩

/-- **Halving descent**: a common point at depth `L+1` yields one at depth
`L` (floors held at `L`).  The reduced witness halves; the window
recursion turns the arc bookkeeping into `⌊(φ + b)/2⌋ ≤ q·H+L+2`. -/
theorem coneCommonPoint_of_succ {H L : ℕ} {Q : List ℕ}
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (h : coneCommonPoint H (L + 1) Q) : coneCommonPoint H L Q := by
  obtain ⟨y, hy⟩ := h
  have h2L : (0 : ℤ) < 2 ^ L := by positivity
  have h2L1 : (0 : ℤ) < 2 ^ (L + 1) := by positivity
  refine ⟨y % 2 ^ (L + 1) / 2, fun q hq => ?_⟩
  have hb := hy q hq
  set P1 : ℤ := (windowNumerator (q * H) (L + 1) : ℤ) with hP1
  set P0 : ℤ := (windowNumerator (q * H) L : ℤ) with hP0
  set b : ℤ := (y - P1) % 2 ^ (L + 1) with hbdef
  have hbnn : (0 : ℤ) ≤ b := Int.emod_nonneg _ (ne_of_gt h2L1)
  set f : ℤ := (Nat.totient (q * H + 1 + L) : ℤ) with hf
  have hfnn : (0 : ℤ) ≤ f := by rw [hf]; positivity
  have hfle : f ≤ q * H + L + 1 := by
    have hnat : (q * H + 1 + L).totient ≤ q * H + L + 1 := by
      have := Nat.totient_le (q * H + 1 + L)
      omega
    rw [hf]
    exact_mod_cast hnat
  have hrec : P1 = 2 * P0 + f := by
    rw [hP1, hP0, hf, windowNumerator_succ]
    push_cast
    ring
  -- y = (2·P0 + f + b) + 2^{L+1}·D
  have hdiv := Int.ediv_add_emod (y - P1) (2 ^ (L + 1))
  set D : ℤ := (y - P1) / 2 ^ (L + 1) with hD
  have hy_eq : y = 2 * P0 + f + b + 2 ^ (L + 1) * D := by
    have hyy : y - P1 = 2 ^ (L + 1) * D + b := hdiv.symm
    rw [hrec] at hyy
    linarith
  set m : ℤ := 2 * P0 + f + b with hm
  have hymod : y % 2 ^ (L + 1) = m % 2 ^ (L + 1) := by
    rw [hy_eq]
    exact Int.add_mul_emod_self_left m (2 ^ (L + 1)) D
  -- peel the reduced witness: m % 2^{L+1} = (f+b) + 2·(P0 − 2^L·K)
  have hKdiv := Int.ediv_add_emod m (2 ^ (L + 1))
  set K : ℤ := m / 2 ^ (L + 1) with hK
  have hmsplit : m % 2 ^ (L + 1) = f + b + 2 * (P0 - 2 ^ L * K) := by
    have h2pow : (2 : ℤ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have : m % 2 ^ (L + 1) = m - 2 ^ (L + 1) * K := by linarith [hKdiv]
    rw [this, hm, h2pow]
    ring
  have hzsplit : y % 2 ^ (L + 1) / 2 = (f + b) / 2 + (P0 - 2 ^ L * K) := by
    rw [hymod, hmsplit]
    exact Int.add_mul_ediv_left (f + b) (P0 - 2 ^ L * K) two_ne_zero
  -- arc bookkeeping at depth L
  have hwnn : (0 : ℤ) ≤ f + b := by linarith
  have hwle : f + b ≤ 2 * (q * H + L + 2) := by
    have hble : b ≤ q * H + (L + 1) + 2 := hb
    linarith
  have hhalf_nn : (0 : ℤ) ≤ (f + b) / 2 :=
    Int.ediv_nonneg hwnn (by norm_num)
  have hhalf_le : (f + b) / 2 ≤ q * H + L + 2 := by
    have hstep : (f + b) / 2 ≤ 2 * (q * H + L + 2) / 2 :=
      Int.ediv_le_ediv (by norm_num) hwle
    rwa [Int.mul_ediv_cancel_left _ two_ne_zero] at hstep
  have hgoal : (y % 2 ^ (L + 1) / 2 - P0) % 2 ^ L = (f + b) / 2 := by
    have hshape : y % 2 ^ (L + 1) / 2 - P0 = (f + b) / 2 + 2 ^ L * (-K) := by
      rw [hzsplit]; ring
    rw [hshape, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hhalf_nn
      (lt_of_le_of_lt hhalf_le (hfloor q hq))
  rw [hgoal]
  exact hhalf_le

/-- The one-sided floor propagates up one depth bit. -/
lemma coneNonflat_floor_succ {H q L : ℕ}
    (h : (q * H + L + 2 : ℤ) < 2 ^ L) :
    (q * H + (L + 1) + 2 : ℤ) < 2 ^ (L + 1) := by
  have hqh : (0 : ℤ) ≤ (q * H : ℤ) := by positivity
  have h2 : (2 : ℤ) ^ (L + 1) = 2 * 2 ^ L := by ring
  rw [h2]
  linarith

/-- The one-sided floor propagates to every larger depth. -/
lemma coneNonflat_floor_mono {H q L L' : ℕ} (hle : L ≤ L')
    (h : (q * H + L + 2 : ℤ) < 2 ^ L) :
    (q * H + L' + 2 : ℤ) < 2 ^ L' := by
  induction L', hle using Nat.le_induction with
  | base => exact h
  | succ n hn ih => exact coneNonflat_floor_succ ih

/-- **Depth monotonicity, one bit**: a firing certificate keeps firing one
depth deeper (floors held).  Chain: cert(L) ⟹ no common point at `L`
(argmin) ⟹ no common point at `L+1` (halving) ⟹ cert(L+1)
(completeness). -/
theorem coneNonflatCert_mono_depth {H L : ℕ} {Q : List ℕ} (hQ : Q ≠ [])
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : coneNonflatCert H L Q) : coneNonflatCert H (L + 1) Q :=
  coneNonflatCert_of_not_coneCommonPoint fun hcp =>
    not_coneCommonPoint_of_coneNonflatCert hQ hcert
      (coneCommonPoint_of_succ hfloor hcp)

/-- **Depth monotonicity**: a firing certificate fires at EVERY deeper
depth (floors held at the base).  `nonflat_L_min` is therefore THE firing
threshold: below it silence, at and above it certification.  In any supply
statement `∃L` may be replaced by any canonical large-enough depth. -/
theorem coneNonflatCert_mono_of_le {H L L' : ℕ} {Q : List ℕ} (hQ : Q ≠ [])
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : coneNonflatCert H L Q) (hle : L ≤ L') :
    coneNonflatCert H L' Q := by
  induction L', hle using Nat.le_induction with
  | base => exact hcert
  | succ n hn ih =>
      exact coneNonflatCert_mono_depth hQ
        (fun q hq => coneNonflat_floor_mono hn (hfloor q hq)) ih

/-! ## Menu monotonicity: firing propagates to every supermenu, same depth

The other half of the refuter's order structure, and the sharper one.
Common points only SHRINK when arcs are added: a common point of the
larger menu `Q'` restricts (same witness, fewer constraints) to a common
point of any sub-menu `Q ⊆ Q'`.  So an EMPTY sub-menu intersection stays
empty under supersets — with no depth change and no floor condition.  This
is the exact reason the wave-25 joint wins exist (a menu can fire while
every sub-menu is silent: firing runs UPWARD in the menu, not down), and it
collapses the six-arc supply obligation onto the smallest prefix that
already fires. -/

/-- A common point of a menu restricts to a common point of any sub-menu:
the same witness satisfies fewer arc constraints. -/
theorem coneCommonPoint_subset {H L : ℕ} {Q Q' : List ℕ}
    (hsub : ∀ q ∈ Q, q ∈ Q') (h : coneCommonPoint H L Q') :
    coneCommonPoint H L Q := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, fun q hq => hy q (hsub q hq)⟩

/-- **Menu monotonicity, same depth, no floor**: a firing certificate keeps
firing for every supermenu at the SAME depth.  If the sub-menu arcs already
have empty intersection, adding arcs cannot refill it. -/
theorem coneNonflatCert_supermenu {H L : ℕ} {Q Q' : List ℕ} (hQ : Q ≠ [])
    (hsub : ∀ q ∈ Q, q ∈ Q') (hcert : coneNonflatCert H L Q) :
    coneNonflatCert H L Q' :=
  coneNonflatCert_of_not_coneCommonPoint fun hcp =>
    not_coneCommonPoint_of_coneNonflatCert hQ hcert
      (coneCommonPoint_subset hsub hcp)

/-- **The seed-lift theorem**: a small seed menu `Q` firing at its own floor
`L` inflates to every supermenu `Q'` at every deeper depth `L'`.  Depth
monotonicity carries the seed up to `L'`; menu monotonicity carries it out
to `Q'`.  Consequence for supply: it suffices that SOME prefix seed fires
at its floor for arbitrarily large `t` — the full menu at the full depth
follows for free, at no extra arithmetic cost. -/
theorem coneNonflatCert_seed_lift {H L L' : ℕ} {Q Q' : List ℕ} (hQ : Q ≠ [])
    (hsub : ∀ q ∈ Q, q ∈ Q')
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : coneNonflatCert H L Q) (hle : L ≤ L') :
    coneNonflatCert H L' Q' :=
  coneNonflatCert_supermenu hQ hsub
    (coneNonflatCert_mono_of_le hQ hfloor hcert hle)

/-! ## Kernel-decided deposits: the measured verdicts, machine-checked -/

/-- First firing menus: the non-flatness certificate fires at
`(t, Q, L) = (1, [1,2,3], 5)`, `(2, [1,2,3,4], 5)`, `(3, [1,2,3], 6)` —
the probe-tabulated cells with the smallest totient arguments (all
one-sided floors hold). -/
theorem coneNonflatCert_cells :
    coneNonflatCert (periodLcm 1) 5 [1, 2, 3]
      ∧ coneNonflatCert (periodLcm 2) 5 [1, 2, 3, 4]
      ∧ coneNonflatCert (periodLcm 3) 6 [1, 2, 3] := by decide

/-- **The measured strict win, kernel-checked**: at `t = 2` the menu
`[1, 3]` refutes joint flatness at depth `8`, while NO pairwise
certificate exists at any depth `≤ 8` — the pair first kills at depth `9`.
The one-sided menu band is strictly sharper than the two-sided pairwise
band (probe v3: 30 strict wins among the named menus, 169 in the
exhaustive search). -/
theorem cone_nonflat_strict_win_at_cell :
    coneNonflatCert (periodLcm 2) 8 [1, 3]
      ∧ (∀ L ∈ Finset.Icc 1 8, ¬ certifiedKill (2 * periodLcm 2) (1 * periodLcm 2) L)
      ∧ certifiedKill (2 * periodLcm 2) (1 * periodLcm 2) 9 := by decide

/-- **The measured joint win, kernel-checked**: at `t = 2` the menu
`[2, 3, 4]` refutes joint flatness at depth `5` while EVERY 2-vertex
submenu refuter is silent at depth `5` and every pairwise certificate fails
there too.  The refutation is genuinely joint: the menu is inconsistent at
a depth where every pair alone stays consistent.  (Probe v3 tabulates 52
such joint cells over `t ≤ 7`, menus `⊆ {1..8}`; the named-menu census
cell at `t = 8`, menu `[1,2,3,4]`, fires at depth 12 — its one-sided
floor, slack ZERO — with the same joint silence.) -/
theorem cone_nonflat_joint_win_at_cell :
    coneNonflatCert (periodLcm 2) 5 [2, 3, 4]
      ∧ (¬ coneNonflatCert (periodLcm 2) 5 [2, 3])
      ∧ (¬ coneNonflatCert (periodLcm 2) 5 [2, 4])
      ∧ (¬ coneNonflatCert (periodLcm 2) 5 [3, 4])
      ∧ (¬ certifiedKill (1 * periodLcm 2) (2 * periodLcm 2) 5)
      ∧ (¬ certifiedKill (2 * periodLcm 2) (2 * periodLcm 2) 5)
      ∧ (¬ certifiedKill (1 * periodLcm 2) (3 * periodLcm 2) 5) := by decide

end TotientTailPeriodKiller
end Erdos249257
