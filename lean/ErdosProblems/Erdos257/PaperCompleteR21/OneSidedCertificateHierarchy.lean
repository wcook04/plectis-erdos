import Erdos249257.HalfCutLocator
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralTargetGap
import Mathlib.Computability.Halting

/-!
Paper-form restatement of the long Erdős #257 environment `thm:one-sided`
("One-sidedness", `paper/reasoning-parts/erdos257/a257_front.tex`, line 1509).

The paper asserts three propositions.

* Non-membership of `1/2` in the Mersenne achievement set has an effectively
  checkable finite-certificate formulation, hence a `Σ⁰₁` formulation.
* Membership has the complementary `Π⁰₁` formulation.
* Survival through a tested finite depth alone does not establish membership.

The first two are one statement about one predicate: we build an explicit
natural-number predicate `HalfFatalCertificateCode`, prove it primitive
recursive (hence `ComputablePred`, which is exactly "effectively checkable"),
and prove that non-membership is `∃ n, HalfFatalCertificateCode n` while
membership is `∀ n, ¬ HalfFatalCertificateCode n`.

The certificate is the paper's own: a finite word `u ⊆ {1, …, d}` whose value
already overshoots after skipping rank `d+1`, made effective by replacing the
real tail `R_{d+1}` with a rational upper bound. The paper cuts the tail at a
cutoff and adds `2^{-M} + (2/3)4^{-M}`; we use the sharper enclosure already in
the tree, `mersenneTail N < mersenneWeight N`, which keeps every certificate
inequality an exact comparison of natural numbers after clearing the single
denominator `2 ∏_{k=1}^{N}(2^k - 1)`.

The closing sentence of the environment — that the arithmetical-hierarchy form
by itself proves neither undecidability nor the absence of finite proofs — is a
scope remark about what the classification does not entail, not a proposition
about the achievement set, and is not formalised.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR20

/-! ## The exact natural-number certificate -/

/-- The common denominator `∏_{k=1}^{N} (2^k - 1)`. -/
def mersenneDen (N : ℕ) : ℕ := ∏ k ∈ Finset.range N, (2 ^ (k + 1) - 1)

/-- `2 * mersenneDen N * mersenneWeight n`, an exact natural number whenever
`1 ≤ n ≤ N`. -/
def scaledMersenneWeight (N n : ℕ) : ℕ := (2 * mersenneDen N) / (2 ^ n - 1)

/-- The scaled value of the finite word coded by a list of bits: bit `i` of the
list selects the Mersenne exponent `i + 1`. -/
def certifiedWordValue (L : List Bool) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range L.length,
    bif L.getD i false then scaledMersenneWeight N (i + 1) else 0

/-- The scaled rational upper bound for the tail `mersenneTail (d+1)`: the exact
weights of ranks `d+2, …, N` plus the enclosure `mersenneTail N < mersenneWeight N`. -/
def certifiedTailBound (d N : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (N - (d + 1)), scaledMersenneWeight N (d + 1 + 1 + j))
    + scaledMersenneWeight N N

/-- The finite certificate: a bit word of length `d`, a cutoff `N ≥ d + 1`, and
two exact natural-number inequalities saying that the coded word already
overshoots `1/2` after the skip at rank `d + 1`. -/
def FatalHalfGapCertificate (p : List Bool × ℕ) : Prop :=
  p.1.length + 1 ≤ p.2 ∧
    certifiedWordValue p.1 p.2 + certifiedTailBound p.1.length p.2 < mersenneDen p.2 ∧
      mersenneDen p.2 <
        certifiedWordValue p.1 p.2 + scaledMersenneWeight p.2 (p.1.length + 1)

instance decidableFatalHalfGapCertificate (p : List Bool × ℕ) :
    Decidable (FatalHalfGapCertificate p) := by
  unfold FatalHalfGapCertificate
  infer_instance

/-- The finite Mersenne word coded by a list of bits. -/
def certWord (L : List Bool) : Finset ℕ :=
  ((Finset.range L.length).filter fun i => L.getD i false = true).image (· + 1)

/-! ## Exactness of the scaled weights -/

theorem mersenneDen_pos (N : ℕ) : 0 < mersenneDen N := by
  refine Finset.prod_pos fun k _ => ?_
  have h : 2 ≤ 2 ^ (k + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private theorem cast_two_pow_sub_one (n : ℕ) :
    ((2 ^ n - 1 : ℕ) : ℝ) = (2 : ℝ) ^ n - 1 := by
  have h : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  rw [Nat.cast_sub h]
  push_cast
  ring

private theorem two_pow_sub_one_dvd {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (2 ^ n - 1) ∣ 2 * mersenneDen N := by
  have hmem : n - 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have hdvd := Finset.dvd_prod_of_mem (fun k : ℕ => 2 ^ (k + 1) - 1) hmem
  simp only [Nat.sub_add_cancel hn] at hdvd
  exact Dvd.dvd.mul_left hdvd 2

theorem scaledMersenneWeight_cast {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (scaledMersenneWeight N n : ℝ) = 2 * (mersenneDen N : ℝ) * mersenneWeight n := by
  have hmul : scaledMersenneWeight N n * (2 ^ n - 1) = 2 * mersenneDen N :=
    Nat.div_mul_cancel (two_pow_sub_one_dvd hn hnN)
  have hcast : (scaledMersenneWeight N n : ℝ) * ((2 : ℝ) ^ n - 1)
      = 2 * (mersenneDen N : ℝ) := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hmul
    simpa [cast_two_pow_sub_one] using this
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by
    have h1 : (1 : ℝ) < 2 ^ n := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
    linarith
  rw [mersenneWeight]
  field_simp
  linarith [hcast]

/-! ## The coded word -/

theorem certWord_bounds (L : List Bool) : ∀ n ∈ certWord L, 0 < n ∧ n ≤ L.length := by
  intro n hn
  rw [certWord, Finset.mem_image] at hn
  obtain ⟨i, hi, rfl⟩ := hn
  rw [Finset.mem_filter, Finset.mem_range] at hi
  exact ⟨Nat.succ_pos i, by omega⟩

private theorem certWord_sum (L : List Bool) :
    ∑ n ∈ certWord L, mersenneWeight n
      = ∑ i ∈ Finset.range L.length,
          (if L.getD i false = true then mersenneWeight (i + 1) else 0) := by
  rw [certWord, Finset.sum_image (by intro x _ y _ h; simpa using h), Finset.sum_filter]

theorem certifiedWordValue_cast {L : List Bool} {N : ℕ} (hLN : L.length ≤ N) :
    (certifiedWordValue L N : ℝ)
      = 2 * (mersenneDen N : ℝ) * ∑ n ∈ certWord L, mersenneWeight n := by
  rw [certWord_sum, Finset.mul_sum, certifiedWordValue, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < L.length := Finset.mem_range.mp hi
  cases h : L.getD i false
  · simp
  · simp only [cond_true, if_true]
    exact scaledMersenneWeight_cast (Nat.succ_pos i) (by omega)

theorem certifiedTailBound_cast {d N : ℕ} (hdN : d + 1 ≤ N) :
    (certifiedTailBound d N : ℝ)
      = 2 * (mersenneDen N : ℝ) *
          ((∑ j ∈ Finset.range (N - (d + 1)), mersenneWeight (d + 1 + 1 + j))
            + mersenneWeight N) := by
  rw [certifiedTailBound]
  push_cast
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < N - (d + 1) := Finset.mem_range.mp hj
    exact scaledMersenneWeight_cast (by omega) (by omega)
  · exact scaledMersenneWeight_cast (by omega) le_rfl

/-! ## The tail split -/

theorem mersenneTail_eq_sum_add (m K : ℕ) :
    mersenneTail m
      = (∑ j ∈ Finset.range K, mersenneWeight (m + 1 + j)) + mersenneTail (m + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
      have h := mersenneTail_eq_weight_add (m + K)
      have hidx : m + 1 + K = m + K + 1 := by omega
      have hidx2 : m + (K + 1) = m + K + 1 := by omega
      rw [Finset.sum_range_succ, ih, hidx, h, hidx2]
      ring

/-! ## Soundness: a certificate produces a fatal half gap -/

theorem existsFatalHalfGap_of_certificate {L : List Bool} {N : ℕ}
    (h : FatalHalfGapCertificate (L, N)) : ExistsFatalHalfGap := by
  obtain ⟨hdN, hlow, hhigh⟩ := h
  have hdN' : L.length + 1 ≤ N := hdN
  have hDpos : (0 : ℝ) < (mersenneDen N : ℝ) := by exact_mod_cast mersenneDen_pos N
  have hVcast := certifiedWordValue_cast (L := L) (N := N) (by omega)
  have hTcast := certifiedTailBound_cast (d := L.length) (N := N) hdN'
  have hWcast := scaledMersenneWeight_cast (N := N) (n := L.length + 1)
    (Nat.succ_pos _) hdN'
  have hlowR : (certifiedWordValue L N : ℝ) + (certifiedTailBound L.length N : ℝ)
      < (mersenneDen N : ℝ) := by exact_mod_cast hlow
  have hhighR : (mersenneDen N : ℝ)
      < (certifiedWordValue L N : ℝ) + (scaledMersenneWeight N (L.length + 1) : ℝ) := by
    exact_mod_cast hhigh
  rw [hVcast, hTcast] at hlowR
  rw [hVcast, hWcast] at hhighR
  set V := ∑ n ∈ certWord L, mersenneWeight n with hV
  set S := ∑ j ∈ Finset.range (N - (L.length + 1)),
    mersenneWeight (L.length + 1 + 1 + j) with hS
  have hkey1 : V + S + mersenneWeight N < 1 / 2 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hkey2 : (1 : ℝ) / 2 < V + mersenneWeight (L.length + 1) := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hsplit := mersenneTail_eq_sum_add (L.length + 1) (N - (L.length + 1))
  have hNN : L.length + 1 + (N - (L.length + 1)) = N := by omega
  rw [hNN] at hsplit
  have htailLt : mersenneTail (L.length + 1) < S + mersenneWeight N := by
    rw [hsplit, ← hS]
    have := mersenneTail_lt_weight (n := N) (by omega)
    linarith
  refine ⟨certWord L, L.length, certWord_bounds L, ?_, ?_⟩
  · rw [positiveMersenneSupportValue_coe_finset, ← hV]
    linarith
  · rw [positiveMersenneSupportValue_coe_finset, ← hV]
    linarith

/-! ## Completeness: a fatal half gap produces a certificate -/

private theorem getD_map_range {d i : ℕ} (f : ℕ → Bool) (hi : i < d) :
    ((List.range d).map f).getD i false = f i := by
  have h1 : ((List.range d).map f)[i]? = some (f i) := by
    simp [hi]
  simp [List.getD_eq_getElem?_getD, h1]

private theorem certWord_encode {u : Finset ℕ} {d : ℕ}
    (hub : ∀ n ∈ u, 0 < n ∧ n ≤ d) :
    certWord ((List.range d).map fun i => decide (i + 1 ∈ u)) = u := by
  have hlen : ((List.range d).map fun i => decide (i + 1 ∈ u)).length = d := by simp
  ext n
  rw [certWord, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range, hlen] at hi
    obtain ⟨hid, hbit⟩ := hi
    rw [getD_map_range _ hid] at hbit
    simpa using hbit
  · intro hn
    obtain ⟨hpos, hle⟩ := hub n hn
    refine ⟨n - 1, ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range, hlen]
    refine ⟨by omega, ?_⟩
    rw [getD_map_range _ (by omega : n - 1 < d)]
    have : n - 1 + 1 = n := by omega
    simp [this, hn]

theorem certificate_of_existsFatalHalfGap (h : ExistsFatalHalfGap) :
    ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := by
  obtain ⟨u, d, hub, hlo, hhi⟩ := h
  rw [positiveMersenneSupportValue_coe_finset] at hlo hhi
  set V := ∑ n ∈ u, mersenneWeight n with hV
  have hε : 0 < 1 / 2 - V - mersenneTail (d + 1) := by linarith
  have hev : ∀ᶠ m in Filter.atTop, mersenneTail m < 1 / 2 - V - mersenneTail (d + 1) :=
    tendsto_mersenneTail_zero (gt_mem_nhds hε)
  obtain ⟨n, hn1, hn2⟩ := (hev.and (Filter.eventually_ge_atTop d)).exists
  set N := n + 1 with hN
  set L := (List.range d).map (fun i => decide (i + 1 ∈ u)) with hL
  have hlen : L.length = d := by simp [hL]
  have hword : certWord L = u := certWord_encode hub
  have hdN : d + 1 ≤ N := by omega
  have hwle : mersenneWeight N ≤ mersenneTail n := by
    have h := mersenneTail_eq_weight_add n
    have h2 := mersenneTail_nonneg (n + 1)
    rw [hN]
    linarith
  have hwsmall : mersenneWeight N < 1 / 2 - V - mersenneTail (d + 1) := by linarith
  have hDpos : (0 : ℝ) < (mersenneDen N : ℝ) := by exact_mod_cast mersenneDen_pos N
  have hsplit := mersenneTail_eq_sum_add (d + 1) (N - (d + 1))
  have hNN : d + 1 + (N - (d + 1)) = N := by omega
  rw [hNN] at hsplit
  set S := ∑ j ∈ Finset.range (N - (d + 1)), mersenneWeight (d + 1 + 1 + j) with hS
  have hSle : S ≤ mersenneTail (d + 1) := by
    have := mersenneTail_nonneg N
    linarith [hsplit]
  have hVcast := certifiedWordValue_cast (L := L) (N := N) (by omega)
  have hTcast := certifiedTailBound_cast (d := d) (N := N) hdN
  have hWcast := scaledMersenneWeight_cast (N := N) (n := d + 1) (Nat.succ_pos d) hdN
  rw [hword, ← hV] at hVcast
  rw [← hS] at hTcast
  refine ⟨(L, N), ?_, ?_, ?_⟩
  · simpa [hlen] using hdN
  · have hreal : (certifiedWordValue L N : ℝ) + (certifiedTailBound d N : ℝ)
        < (mersenneDen N : ℝ) := by
      rw [hVcast, hTcast]
      nlinarith
    simp only [hlen]
    exact_mod_cast hreal
  · have hreal : (mersenneDen N : ℝ)
        < (certifiedWordValue L N : ℝ) + (scaledMersenneWeight N (d + 1) : ℝ) := by
      rw [hVcast, hWcast]
      nlinarith
    simp only [hlen]
    exact_mod_cast hreal

theorem existsFatalHalfGap_iff_exists_certificate :
    ExistsFatalHalfGap ↔ ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := by
  constructor
  · exact certificate_of_existsFatalHalfGap
  · rintro ⟨⟨L, N⟩, h⟩
    exact existsFatalHalfGap_of_certificate h

/-! ## The certificate predicate is primitive recursive -/

private theorem foldr_range_add (f : ℕ → ℕ) : ∀ (n c : ℕ),
    (List.range n).foldr (fun i s => f i + s) c = (∑ i ∈ Finset.range n, f i) + c := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
      intro c
      rw [List.range_succ, List.foldr_append, ih, Finset.sum_range_succ]
      simp [add_assoc]

private theorem foldr_range_mul (f : ℕ → ℕ) : ∀ (n c : ℕ),
    (List.range n).foldr (fun i s => f i * s) c = (∏ i ∈ Finset.range n, f i) * c := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
      intro c
      rw [List.range_succ, List.foldr_append, ih, Finset.prod_range_succ]
      simp [mul_assoc]

private theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

private theorem primrec_mersenneDen : Primrec mersenneDen := by
  have hh : Primrec₂ (fun (_ : ℕ) (q : ℕ × ℕ) => (2 ^ (q.1 + 1) - 1) * q.2) :=
    Primrec.nat_mul.comp
      (Primrec.nat_sub.comp
        (primrec_natPow.comp (Primrec.const 2)
          (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
        (Primrec.const 1))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr Primrec.list_range (Primrec.const 1) hh
  refine h.of_eq fun N => ?_
  have := foldr_range_mul (fun k : ℕ => 2 ^ (k + 1) - 1) N 1
  simpa [mersenneDen] using this

private theorem primrec_scaledWeight : Primrec₂ scaledMersenneWeight :=
  Primrec.nat_div.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (primrec_mersenneDen.comp Primrec.fst))
    (Primrec.nat_sub.comp (primrec_natPow.comp (Primrec.const 2) Primrec.snd)
      (Primrec.const 1))

private theorem primrec_certifiedWordValue :
    Primrec fun p : List Bool × ℕ => certifiedWordValue p.1 p.2 := by
  have hh : Primrec₂ (fun (a : List Bool × ℕ) (q : ℕ × ℕ) =>
      (bif a.1.getD q.1 false then scaledMersenneWeight a.2 (q.1 + 1) else 0) + q.2) := by
    refine Primrec.nat_add.comp ?_ (Primrec.snd.comp Primrec.snd)
    refine Primrec.cond ?_ ?_ (Primrec.const 0)
    · exact (Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd)
    · exact primrec_scaledWeight.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
  have h := Primrec.list_foldr
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
    (Primrec.const 0) hh
  refine h.of_eq fun p => ?_
  have := foldr_range_add
    (fun i => bif p.1.getD i false then scaledMersenneWeight p.2 (i + 1) else 0)
    p.1.length 0
  simpa [certifiedWordValue] using this

private theorem primrec_certifiedTailBound : Primrec₂ certifiedTailBound := by
  have hh : Primrec₂ (fun (a : ℕ × ℕ) (q : ℕ × ℕ) =>
      scaledMersenneWeight a.2 (a.1 + 1 + 1 + q.1) + q.2) := by
    refine Primrec.nat_add.comp ?_ (Primrec.snd.comp Primrec.snd)
    exact primrec_scaledWeight.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1))
          (Primrec.const 1))
        (Primrec.fst.comp Primrec.snd))
  have hsum := Primrec.list_foldr
    (Primrec.list_range.comp
      (Primrec.nat_sub.comp Primrec.snd
        (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))))
    (Primrec.const 0) hh
  have h : Primrec fun a : ℕ × ℕ =>
      (List.range (a.2 - (a.1 + 1))).foldr
        (fun j s => scaledMersenneWeight a.2 (a.1 + 1 + 1 + j) + s) 0
        + scaledMersenneWeight a.2 a.2 :=
    Primrec.nat_add.comp hsum (primrec_scaledWeight.comp Primrec.snd Primrec.snd)
  refine h.of_eq fun a => ?_
  have := foldr_range_add
    (fun j => scaledMersenneWeight a.2 (a.1 + 1 + 1 + j)) (a.2 - (a.1 + 1)) 0
  simp [certifiedTailBound, this]

private theorem primrecPred_certificate : PrimrecPred FatalHalfGapCertificate := by
  have hword : Primrec fun p : List Bool × ℕ => certifiedWordValue p.1 p.2 :=
    primrec_certifiedWordValue
  have hlen : Primrec fun p : List Bool × ℕ => p.1.length + 1 :=
    Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 1)
  have htail : Primrec fun p : List Bool × ℕ => certifiedTailBound p.1.length p.2 :=
    primrec_certifiedTailBound.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd
  have hden : Primrec fun p : List Bool × ℕ => mersenneDen p.2 :=
    primrec_mersenneDen.comp Primrec.snd
  have hw : Primrec fun p : List Bool × ℕ => scaledMersenneWeight p.2 (p.1.length + 1) :=
    primrec_scaledWeight.comp Primrec.snd hlen
  exact (PrimrecRel.comp Primrec.nat_le hlen Primrec.snd).and
    ((PrimrecRel.comp Primrec.nat_lt (Primrec.nat_add.comp hword htail) hden).and
      (PrimrecRel.comp Primrec.nat_lt hden (Primrec.nat_add.comp hword hw)))

/-! ## The `Σ⁰₁` predicate on the naturals -/

/-- The certificate search recast as a decidable predicate on a single natural
number: `n` codes a pair `(word, cutoff)` that certifies the fatal gap. -/
def halfFatalCertificateCheck (n : ℕ) : Bool :=
  (Encodable.decode (α := List Bool × ℕ) n).elim false
    fun p => decide (FatalHalfGapCertificate p)

/-- The `Σ⁰₁` matrix: an effectively checkable property of one natural number. -/
def HalfFatalCertificateCode (n : ℕ) : Prop := halfFatalCertificateCheck n = true

instance decidableHalfFatalCertificateCode : DecidablePred HalfFatalCertificateCode :=
  fun n => inferInstanceAs (Decidable (halfFatalCertificateCheck n = true))

private theorem primrec_check : Primrec halfFatalCertificateCheck := by
  have h := Primrec.option_casesOn
    (o := fun n : ℕ => Encodable.decode (α := List Bool × ℕ) n)
    (f := fun _ : ℕ => false)
    (g := fun (_ : ℕ) (p : List Bool × ℕ) => decide (FatalHalfGapCertificate p))
    Primrec.decode (Primrec.const false)
    (primrecPred_certificate.decide.comp Primrec.snd).to₂
  refine h.of_eq fun n => ?_
  simp only [halfFatalCertificateCheck]
  cases Encodable.decode (α := List Bool × ℕ) n <;> rfl

/-- The certificate matrix is effectively checkable. -/
theorem computablePred_halfFatalCertificateCode :
    ComputablePred HalfFatalCertificateCode := by
  refine PrimrecPred.computablePred (Primrec.primrecPred ?_)
  refine primrec_check.of_eq fun n => ?_
  simp [HalfFatalCertificateCode]

theorem exists_halfFatalCertificateCode_iff :
    (∃ n : ℕ, HalfFatalCertificateCode n) ↔ ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := by
  constructor
  · rintro ⟨n, hn⟩
    rw [HalfFatalCertificateCode, halfFatalCertificateCheck] at hn
    cases hdec : Encodable.decode (α := List Bool × ℕ) n with
    | none => rw [hdec] at hn; simp at hn
    | some p =>
        rw [hdec] at hn
        exact ⟨p, by simpa using hn⟩
  · rintro ⟨p, hp⟩
    refine ⟨Encodable.encode p, ?_⟩
    rw [HalfFatalCertificateCode, halfFatalCertificateCheck, Encodable.encodek]
    simpa using hp

/-! ## The two arithmetical forms -/

/-- Non-membership of `1/2` is exactly the existence of a finite certificate. -/
theorem half_not_mem_iff_exists_halfFatalCertificateCode :
    (1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ∃ n : ℕ, HalfFatalCertificateCode n := by
  rw [exists_halfFatalCertificateCode_iff, ← existsFatalHalfGap_iff_exists_certificate,
    existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet]

/-- Membership of `1/2` is exactly the failure of every finite certificate. -/
theorem half_mem_iff_forall_not_halfFatalCertificateCode :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ∀ n : ℕ, ¬ HalfFatalCertificateCode n := by
  rw [← not_iff_not, not_forall_not, ← half_not_mem_iff_exists_halfFatalCertificateCode]

/-! ## Finite-depth survival is not membership -/

/-- Surviving the straddle test through a tested finite depth does not establish
membership: at every depth there is a target that straddles and is still outside
the achievement set. -/
theorem finite_depth_survival_not_sufficient (d : ℕ) :
    ∃ x : ℝ, IsStraddlePrefix x ∅ d ∧ x ∉ mersenneAchievementSet := by
  set x : ℝ := (mersenneTail (d + 1) + mersenneWeight (d + 1)) / 2 with hx
  have hgap : mersenneTail (d + 1) < mersenneWeight (d + 1) :=
    mersenneTail_lt_weight (by omega)
  have htnn : 0 ≤ mersenneTail (d + 1) := mersenneTail_nonneg (d + 1)
  have hempty : positiveMersenneSupportValue ((∅ : Finset ℕ) : Set ℕ) = 0 := by
    rw [positiveMersenneSupportValue_coe_finset]
    simp
  have hlo : mersenneTail (d + 1) < x := by rw [hx]; linarith
  have hhi : x < mersenneWeight (d + 1) := by rw [hx]; linarith
  have htail := mersenneTail_eq_weight_add d
  refine ⟨x, ⟨by simp, ?_, ?_⟩, ?_⟩
  · rw [hempty]; linarith
  · rw [hempty]; linarith
  · refine internal_gap_excludes_membership ⟨∅, d + 1, by omega, by simp, ?_, ?_⟩
    · rw [hempty]; linarith
    · rw [hempty]; linarith

/-! ## The paper environment -/

/-- Long `thm:one-sided` (One-sidedness).  Non-membership of `1/2` in the
Mersenne achievement set has an effectively checkable finite-certificate
formulation, hence the `Σ⁰₁` form `∃ n, P n` with `P` computable; membership has
the complementary `Π⁰₁` form `∀ n, ¬ P n` over the same `P`; and survival through
a tested finite depth alone does not establish membership. -/
theorem paper_one_sidedness :
    (∃ P : ℕ → Prop, ComputablePred P ∧
        ((1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ∃ n : ℕ, P n) ∧
        ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ∀ n : ℕ, ¬ P n)) ∧
      (∀ d : ℕ, ∃ x : ℝ, IsStraddlePrefix x ∅ d ∧ x ∉ mersenneAchievementSet) :=
  ⟨⟨HalfFatalCertificateCode, computablePred_halfFatalCertificateCode,
      half_not_mem_iff_exists_halfFatalCertificateCode,
      half_mem_iff_forall_not_halfFatalCertificateCode⟩,
    finite_depth_survival_not_sufficient⟩

#print axioms scaledMersenneWeight_cast
#print axioms certifiedWordValue_cast
#print axioms certifiedTailBound_cast
#print axioms mersenneTail_eq_sum_add
#print axioms existsFatalHalfGap_of_certificate
#print axioms certificate_of_existsFatalHalfGap
#print axioms existsFatalHalfGap_iff_exists_certificate
#print axioms computablePred_halfFatalCertificateCode
#print axioms exists_halfFatalCertificateCode_iff
#print axioms half_not_mem_iff_exists_halfFatalCertificateCode
#print axioms half_mem_iff_forall_not_halfFatalCertificateCode
#print axioms finite_depth_survival_not_sufficient
#print axioms paper_one_sidedness

end ErdosProblems.Erdos257.PaperCompleteR21
