/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Erdos249257.DiagonalFreshLossBridge

/-!
# Inducing the lift law from the 28 recorded diagonal certificates

## The corpus audit that motivates this file

The 28 recorded deposits live at

  `t ∈ {1,2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49,53,59,61,64}`

and every one of them is proved the same way: factor the `2L` window integers,
Lucas-certify every prime factor above `10^7`, rebuild each `φ` through
`totient_factorBlocks`, then close `certifiedKill` by one `norm_num` over
`Finset.sum_range_succ`.  Each file's header says it "reuses 0 earlier
certificates", and reading them confirms it: every `phi_tX_…` lemma is `private`,
so it is not even *visible* downstream, and the `certifiedKill_diagonal_tX`
proofs cite no earlier certificate.  The corpus is 28 independent constructions.

That is not the interesting part.  The interesting part is *why*, and it is
measurable.  Writing `W(H,L) = [H+1, H+L] ∪ [2H+1, 2H+L]` for the set of
integers whose totients the cell `certifiedKill H H L` reads, the recorded
consecutive pairs give exactly this table of `|W(H_t, L_t) ∩ W(H_{t'}, L_{t'})|`:

| crossing | `p` | shared window integers |
| --- | --- | --- |
| 19→23, 23→25, 25→27, 27→29, 29→31 | 23, 5, 3, 29, 31 | 0 |
| **31→32** | **2** | **49 = min(L₃₁,L₃₂)** |
| 32→37, …, 59→61 | 37, 41, 43, 47, 7, 53, 59, 61 | 0 |
| **61→64** | **2** | **93 = min(L₆₁,L₆₄)** |

(For 61→64: `H₆₄ = 2·H₆₁ = 1182266884102822267511361600`, and the 93 shared
arguments are `1182266884102822267511361601 … 1182266884102822267511361693`.
`DiagonalPincerCertificatesT64.lean` restates and reproves every one of those 93
totients from scratch, even though `DiagonalPincerCertificatesT61.lean` already
contains the identical statements — and could not do otherwise, since each
`phi_tX_…` is `private`.)

The one place the overlap does leak through is the *primality* layer, which is
pooled in `DiagonalPincerPrimeCertificates`.  Counting shared `prime_lucas_…`
leaves between consecutive files: `31 → 32` shares `33` of `46`, and `61 → 64`
shares `117` of `175` — because the shared window integers have the same
factorisations.  The neighbouring odd rung `59 → 61` shares `2` of `173`.  So the
corpus's entire measurable reuse is a mechanical consequence of the `p = 2`
window overlap formalised below as `diagWindow_inter_two`, and it stops at the
prime leaves: no totient, and no certificate, is ever reused.

So the corpus contains **one** reusable structure and it fires at exactly the
two `p = 2` crossings.  This file states that structure in general, and then
proves the matching negative that explains the zeros in the rest of the column.

## What is proved here

Everything is stated for an *arbitrary* `f : ℕ → ℤ` in place of `Nat.totient`
(`genWindowDiscrepancy`, `genCertifiedKill`), because that is the only way to
say precisely which lifts are impossible: a lift law is a law only if it works
from the certified cell's data, and the certified cell's data is exactly the
restriction of `φ` to `W(H,L)` (`genWindowDiscrepancy_congr_diag`).

1. **Window geometry.**  `diagWindow_disjoint`: if `2H + L ≤ pH` — in particular
   whenever `3 ≤ p` and `L ≤ H` — the cells at `H` and at `pH` share *no*
   argument at all, at any depth `L'` above.  `diagWindow_inter_two`: at `p = 2`
   the intersection is *exactly* the upper block `[2H+1, 2H+L]`, i.e. half the
   lifted cell's data, which is the general form of the two corpus reuses.

2. **The reuse, in block form.**  `genWindowDiscrepancy_eq_blockSum_sub` writes
   every cell as a difference of two block sums, and
   `blockSum_two_mul_congr_diag` says the lifted cell's *lower* block at `p = 2`
   is determined by the certified cell.  The transportable quantum is the block
   sum, not the certificate: `certifiedKill` is an inequality on the difference
   and forgets which block produced it.

3. **The negative that decides the question.**  `no_window_local_lift`: for
   every `p ≥ 3`, every `H > 0` and every `L ≤ H` there is `f : ℕ → ℤ` which
     * agrees with `φ` on the whole certified window `W(H,L)`, hence satisfies
       the *identical* certificate below (`genCertifiedKill f H H L ↔
       certifiedKill H H L`), and
     * has `genWindowDiscrepancy f (pH) (pH) L' = 0` for **every** depth `L'`,
       hence certifies at **no** depth above.

   So, in the arbitrary-sequence model, the certified window below places no
   constraint on the rung above.  No lift of the displayed shape can follow
   from that window data alone.  This does not rule out a theorem using
   arithmetic specific to `Nat.totient`.

   `certified_cell_blind_at_rung` transports this onto the lcm ladder:
   at every prime-power boundary `periodLcm (t+1) = p · periodLcm t` with
   `p ≥ 3` — which is every boundary except `t + 1 = 2^a` — the rung is blind.

4. **The `p = 2` boundaries are the only ones with window overlap, and they are
   sparse.**  `periodLcm_pow_two_eq_two_mul` (DiagonalFreshLossBridge) says the
   doubling boundaries are exactly `t + 1 = 2^a`.  `diagWindow_inter_two_pow`
   instantiates the half-transfer there.  Between two consecutive doubling
   boundaries `2^a` and `2^(a+1)` the ladder must cross every prime power in
   `(2^a, 2^(a+1)]`, and by (3) every one of those crossings is blind.

## What this does not say

`no_window_local_lift` rules out lifts that factor through the certified
window.  It does not rule out a lift that imports genuinely new arithmetic about
`φ` at `pH + d` and `2pH + d` — that is what `Recon67` does by hand at the
`t = 67` rung, at the price of `2L` fresh factorisations.  The content of this
file is that no such route follows from the recorded window values alone.  It
does not prove that every cheaper, totient-specific route is impossible.
-/

namespace ErdosProblems
namespace Lift
namespace InduceLaw

open Erdos249257 Erdos249257.TotientTailPeriodKiller

/-! ## 1. The support of a diagonal cell -/

/-- The **diagonal window** `W(H,L) = [H+1, H+L] ∪ [2H+1, 2H+L]`: the `2L`
integers whose totients the cell `certifiedKill H H L` reads. -/
def diagWindow (H L : ℕ) : Finset ℕ :=
  (Finset.range L).image (fun j => H + 1 + j) ∪
    (Finset.range L).image (fun j => 2 * H + 1 + j)

lemma mem_diagWindow_lower {H L j : ℕ} (hj : j < L) : H + 1 + j ∈ diagWindow H L := by
  simp only [diagWindow, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  exact Or.inl ⟨j, hj, rfl⟩

lemma mem_diagWindow_upper {H L j : ℕ} (hj : j < L) : 2 * H + 1 + j ∈ diagWindow H L := by
  simp only [diagWindow, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  exact Or.inr ⟨j, hj, rfl⟩

lemma diagWindow_bounds {H L n : ℕ} (hn : n ∈ diagWindow H L) :
    H + 1 ≤ n ∧ n ≤ 2 * H + L := by
  simp only [diagWindow, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hn
  rcases hn with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> omega

/-! ## 2. The window functional over an arbitrary coefficient sequence -/

/-- `windowDiscrepancy` with `Nat.totient` replaced by an arbitrary `f : ℕ → ℤ`. -/
def genWindowDiscrepancy (f : ℕ → ℤ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (f (N + h + 1 + j) - f (N + 1 + j)) * 2 ^ (L - 1 - j)

/-- `certifiedKill` with `Nat.totient` replaced by an arbitrary `f : ℕ → ℤ`. -/
def genCertifiedKill (f : ℕ → ℤ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < genWindowDiscrepancy f h N L % 2 ^ L ∧
    genWindowDiscrepancy f h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

@[simp] theorem genWindowDiscrepancy_totient (h N L : ℕ) :
    genWindowDiscrepancy (fun n => (Nat.totient n : ℤ)) h N L = windowDiscrepancy h N L := rfl

@[simp] theorem genCertifiedKill_totient (h N L : ℕ) :
    genCertifiedKill (fun n => (Nat.totient n : ℤ)) h N L ↔ certifiedKill h N L := Iff.rfl

/-- The window functional is additive in the coefficient sequence. -/
theorem genWindowDiscrepancy_add (f g : ℕ → ℤ) (h N L : ℕ) :
    genWindowDiscrepancy (fun n => f n + g n) h N L
      = genWindowDiscrepancy f h N L + genWindowDiscrepancy g h N L := by
  unfold genWindowDiscrepancy
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Locality of the certificate.**  The diagonal cell at `(H, L)` is a function of the
restriction of the coefficient sequence to `diagWindow H L`, and of nothing else.  This
is what makes `diagWindow` the right notion of "the certified cell's data". -/
theorem genWindowDiscrepancy_congr_diag {f g : ℕ → ℤ} (H L : ℕ)
    (hfg : ∀ n ∈ diagWindow H L, f n = g n) :
    genWindowDiscrepancy f H H L = genWindowDiscrepancy g H H L := by
  unfold genWindowDiscrepancy
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjL : j < L := Finset.mem_range.mp hj
  have hup : H + H + 1 + j = 2 * H + 1 + j := by omega
  rw [hup, hfg _ (mem_diagWindow_upper hjL), hfg _ (mem_diagWindow_lower hjL)]

/-- The certificate below is preserved by any coefficient change off its own window. -/
theorem genCertifiedKill_congr_diag {f g : ℕ → ℤ} (H L : ℕ)
    (hfg : ∀ n ∈ diagWindow H L, f n = g n) :
    genCertifiedKill f H H L ↔ genCertifiedKill g H H L := by
  unfold genCertifiedKill
  rw [genWindowDiscrepancy_congr_diag H L hfg]

/-! ## 3. Window geometry across a rung -/

/-- **Rung disjointness.**  If the certified cell fits below the new height —
`2H + L ≤ pH`, which holds whenever `3 ≤ p` and `L ≤ H` — then the cell at `H`
and the cell at `pH` share no argument whatsoever, at *any* depth `L'`. -/
theorem diagWindow_disjoint {p H L L' : ℕ} (hfit : 2 * H + L ≤ p * H) :
    Disjoint (diagWindow H L) (diagWindow (p * H) L') := by
  refine Finset.disjoint_left.mpr fun n hn hn' => ?_
  have h1 := (diagWindow_bounds hn).2
  have h2 := (diagWindow_bounds hn').1
  omega

/-- The usable form: every odd prime rung is disjoint. -/
theorem diagWindow_disjoint_of_three_le {p H L L' : ℕ} (hp : 3 ≤ p) (hL : L ≤ H) :
    Disjoint (diagWindow H L) (diagWindow (p * H) L') := by
  refine diagWindow_disjoint ?_
  have : 3 * H ≤ p * H := Nat.mul_le_mul_right H hp
  omega

/-- **The `p = 2` overlap, exactly.**  At a doubling boundary the two cells share
precisely the upper block `[2H+1, 2H+L]` of the lower one — which is precisely the
lower block of the upper one.  This is the general form of the 49 shared integers at
`31 → 32` and the 93 shared integers at `61 → 64`. -/
theorem diagWindow_inter_two (H L : ℕ) (hL : L ≤ H) :
    diagWindow H L ∩ diagWindow (2 * H) L
      = (Finset.range L).image (fun j => 2 * H + 1 + j) := by
  ext n
  simp only [Finset.mem_inter, diagWindow, Finset.mem_union, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨hlow, hhigh⟩
    rcases hlow with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exfalso
      rcases hhigh with ⟨b, hb, hb'⟩ | ⟨b, hb, hb'⟩ <;> omega
    · exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Or.inr ⟨a, ha, rfl⟩, Or.inl ⟨a, ha, rfl⟩⟩

/-! ## 4. Block form: what the `p = 2` overlap actually transports -/

/-- The block sum `B_f(N,L) = ∑_{j<L} f(N+1+j)·2^{L-1-j}`. -/
def blockSum (f : ℕ → ℤ) (N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, f (N + 1 + j) * 2 ^ (L - 1 - j)

/-- Every cell is a difference of two blocks. -/
theorem genWindowDiscrepancy_eq_blockSum_sub (f : ℕ → ℤ) (h N L : ℕ) :
    genWindowDiscrepancy f h N L = blockSum f (N + h) L - blockSum f N L := by
  unfold genWindowDiscrepancy blockSum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The diagonal cell at height `H` is `B(2H) - B(H)`. -/
theorem genWindowDiscrepancy_diag_blocks (f : ℕ → ℤ) (H L : ℕ) :
    genWindowDiscrepancy f H H L = blockSum f (2 * H) L - blockSum f H L := by
  rw [genWindowDiscrepancy_eq_blockSum_sub]
  congr 2
  omega

/-- The doubled diagonal cell is `B(4H) - B(2H)`: its *lower* block is the certified
cell's *upper* block. -/
theorem genWindowDiscrepancy_double_blocks (f : ℕ → ℤ) (H L : ℕ) :
    genWindowDiscrepancy f (2 * H) (2 * H) L
      = blockSum f (4 * H) L - blockSum f (2 * H) L := by
  rw [genWindowDiscrepancy_eq_blockSum_sub]
  congr 2
  omega

/-- **The transported half.**  The block that the two cells share is determined by the
certified cell's data.  This — not the certificate — is the reusable quantum, and it is
exactly the `L` totient values the corpus recomputes at `31 → 32` and `61 → 64`. -/
theorem blockSum_two_mul_congr_diag {f g : ℕ → ℤ} (H L : ℕ)
    (hfg : ∀ n ∈ diagWindow H L, f n = g n) :
    blockSum f (2 * H) L = blockSum g (2 * H) L := by
  unfold blockSum
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hfg _ (mem_diagWindow_upper (Finset.mem_range.mp hj))]

/-! ## 5. The negative: an odd rung is blind to the cell below it -/

/-- A cell whose discrepancy vanishes cannot certify: the residue is `0`, and the
exclusion radius `N + h + L + 2` is strictly positive. -/
theorem not_genCertifiedKill_of_eq_zero {f : ℕ → ℤ} {h N L : ℕ}
    (h0 : genWindowDiscrepancy f h N L = 0) : ¬ genCertifiedKill f h N L := by
  rintro ⟨hlt, -⟩
  rw [h0, Int.zero_emod] at hlt
  have hN : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
  have hh : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
  have hL : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  linarith

/-- **No window-local lift across an odd rung.**

There is a coefficient sequence which agrees with `φ` on the *entire* certified window
`W(H,L)` — so it satisfies exactly the same certificate below — and whose cell at the
lifted height `pH` has discrepancy `0` at **every** depth.

Consequently the hypothesis `certifiedKill H H L` constrains the lifted cell not at all:
any implication `certifiedKill H H L → ∃ L', certifiedKill (p*H) (p*H) L'` must consume
information about `φ` outside `W(H,L)`. -/
theorem no_window_local_lift {p H L : ℕ} (hp : 3 ≤ p) (hL : L ≤ H) :
    ∃ f : ℕ → ℤ,
      (∀ n ∈ diagWindow H L, f n = (Nat.totient n : ℤ)) ∧
      (genCertifiedKill f H H L ↔ certifiedKill H H L) ∧
      (∀ L' : ℕ, genWindowDiscrepancy f (p * H) (p * H) L' = 0) ∧
      (∀ L' : ℕ, ¬ genCertifiedKill f (p * H) (p * H) L') := by
  classical
  set f : ℕ → ℤ := fun n => if n ∈ diagWindow H L then (Nat.totient n : ℤ) else 0 with hf
  have hpH : 3 * H ≤ p * H := Nat.mul_le_mul_right H hp
  have hagree : ∀ n ∈ diagWindow H L, f n = (Nat.totient n : ℤ) := by
    intro n hn
    simp only [hf, if_pos hn]
  have hzero : ∀ L' : ℕ, genWindowDiscrepancy f (p * H) (p * H) L' = 0 := by
    intro L'
    unfold genWindowDiscrepancy
    refine Finset.sum_eq_zero fun j _ => ?_
    have hout₁ : p * H + p * H + 1 + j ∉ diagWindow H L := by
      intro hmem
      have := (diagWindow_bounds hmem).2
      omega
    have hout₂ : p * H + 1 + j ∉ diagWindow H L := by
      intro hmem
      have := (diagWindow_bounds hmem).2
      omega
    simp only [hf, if_neg hout₁, if_neg hout₂, sub_self, zero_mul]
  refine ⟨f, hagree, ?_, hzero, fun L' => not_genCertifiedKill_of_eq_zero (hzero L')⟩
  rw [genCertifiedKill_congr_diag H L hagree]
  exact genCertifiedKill_totient H H L

/-- **The blindness, on the lcm ladder.**  At every prime-power boundary of the ladder
whose multiplier is at least `3` — that is, every boundary except `t + 1 = 2^a` — the
certified diagonal cell at scale `t` places no constraint on the diagonal cell at scale
`t + 1`, at any depth. -/
theorem certified_cell_blind_at_rung {t p L : ℕ} (hp : 3 ≤ p)
    (hstep : periodLcm (t + 1) = p * periodLcm t) (hL : L ≤ periodLcm t) :
    ∃ f : ℕ → ℤ,
      (∀ n ∈ diagWindow (periodLcm t) L, f n = (Nat.totient n : ℤ)) ∧
      (genCertifiedKill f (periodLcm t) (periodLcm t) L
        ↔ certifiedKill (periodLcm t) (periodLcm t) L) ∧
      (∀ L' : ℕ, ¬ genCertifiedKill f (periodLcm (t + 1)) (periodLcm (t + 1)) L') := by
  obtain ⟨f, h1, h2, -, h4⟩ := no_window_local_lift (p := p) (H := periodLcm t) (L := L) hp hL
  exact ⟨f, h1, h2, by rw [hstep]; exact h4⟩

/-! ## 6. The doubling boundaries, and why they do not rescue the ladder -/

/-- At the doubling boundaries `t + 1 = 2^a` the two cells share exactly one block:
`L` of the lifted cell's `2L` arguments are already certified data. -/
theorem diagWindow_inter_two_pow {a L : ℕ} (ha : 2 ≤ a) (hL : L ≤ periodLcm (2 ^ a - 1)) :
    diagWindow (periodLcm (2 ^ a - 1)) L ∩ diagWindow (periodLcm (2 ^ a)) L
      = (Finset.range L).image (fun j => 2 * periodLcm (2 ^ a - 1) + 1 + j) := by
  rw [Erdos249257.DiagonalFreshLossBridge.periodLcm_pow_two_eq_two_mul ha]
  exact diagWindow_inter_two _ _ hL

/-- Even at a doubling boundary the *upper* block is untouched by the cell below:
`genWindowDiscrepancy f (2H) (2H) L = B_f(4H,L) - B_f(2H,L)` with only `B_f(2H,L)`
determined.  Two sequences agreeing with `φ` on `W(H,L)` can therefore differ in the
lifted cell by exactly the difference of their `4H` blocks — an unconstrained integer. -/
theorem double_rung_residual {f g : ℕ → ℤ} (H L : ℕ)
    (hfg : ∀ n ∈ diagWindow H L, f n = g n) :
    genWindowDiscrepancy f (2 * H) (2 * H) L - genWindowDiscrepancy g (2 * H) (2 * H) L
      = blockSum f (4 * H) L - blockSum g (4 * H) L := by
  rw [genWindowDiscrepancy_double_blocks, genWindowDiscrepancy_double_blocks,
    blockSum_two_mul_congr_diag H L hfg]
  ring

/-! ## 7. Even the doubling rung is undetermined: any value is reachable

Section 5 kills the odd rungs outright.  The doubling rungs survive that argument
because their lower block *is* certified data (§4), so the perturbation used there is
not available.  They fall to a one-point perturbation instead: the last argument of the
lifted cell's upper block carries place value `2^0 = 1`, so moving `φ` there by `c`
moves the whole cell by `c`, and that argument lies outside `W(H,L)` at every rung
`p ≥ 2`.  Hence the certified cell below is compatible with *every* value of the cell
above, at every rung and every depth. -/

/-- A one-point change at the top argument `M + M + L` of the cell `(M, M, L)` moves the
cell by exactly that amount: the top position carries place value `2^0 = 1`. -/
theorem genWindowDiscrepancy_point_mass (c : ℤ) {M L : ℕ} (hM : 0 < M) (hL : 0 < L) :
    genWindowDiscrepancy (fun n => if n = M + M + L then c else 0) M M L = c := by
  unfold genWindowDiscrepancy
  rw [Finset.sum_eq_single (L - 1)]
  · have h1 : M + M + 1 + (L - 1) = M + M + L := by omega
    have h2 : M + 1 + (L - 1) ≠ M + M + L := by omega
    have h3 : L - 1 - (L - 1) = 0 := by omega
    simp only [if_pos h1, if_neg h2, h3]
    norm_num
  · intro a ha hne
    have haL : a < L := Finset.mem_range.mp ha
    have h1 : M + M + 1 + a ≠ M + M + L := by omega
    have h2 : M + 1 + a ≠ M + M + L := by omega
    simp only [if_neg h1, if_neg h2]
    ring
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

/-- **The rung value is unconstrained, at every rung `p ≥ 2` and every depth `L'`.**

Given any target `v : ℤ` there is a coefficient sequence agreeing with `φ` on the whole
certified window `W(H,L)` — hence satisfying exactly the same certificate below — whose
cell at the lifted height `p·H` has discrepancy `v`.

Together with `no_window_local_lift` this settles the question the recorded corpus poses:
the 28 certificates are 28 independent constructions because no other kind of certificate
was available.  Nothing about the cell at scale `t` restricts the cell at scale `t+1`. -/
theorem rung_value_unconstrained {p H L L' : ℕ} (hp : 2 ≤ p) (hH : 0 < H) (hL : L ≤ H)
    (hL' : 0 < L') (v : ℤ) :
    ∃ f : ℕ → ℤ,
      (∀ n ∈ diagWindow H L, f n = (Nat.totient n : ℤ)) ∧
      (genCertifiedKill f H H L ↔ certifiedKill H H L) ∧
      genWindowDiscrepancy f (p * H) (p * H) L' = v := by
  classical
  have h2H : 2 * H ≤ p * H := Nat.mul_le_mul_right H hp
  have hMpos : 0 < p * H := by omega
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, f = fun n => (Nat.totient n : ℤ)
      + (if n = p * H + p * H + L' then v - windowDiscrepancy (p * H) (p * H) L' else 0) :=
    ⟨_, rfl⟩
  have hout : p * H + p * H + L' ∉ diagWindow H L := by
    intro hmem
    have hb := (diagWindow_bounds hmem).2
    omega
  have hagree : ∀ n ∈ diagWindow H L, f n = (Nat.totient n : ℤ) := by
    intro n hn
    have hne : n ≠ p * H + p * H + L' := fun hEq => hout (hEq ▸ hn)
    rw [hf]
    simp [hne]
  refine ⟨f, hagree, ?_, ?_⟩
  · rw [genCertifiedKill_congr_diag H L hagree]
    exact genCertifiedKill_totient H H L
  · have hadd := genWindowDiscrepancy_add (fun n => (Nat.totient n : ℤ))
      (fun n => if n = p * H + p * H + L' then
        v - windowDiscrepancy (p * H) (p * H) L' else 0) (p * H) (p * H) L'
    rw [hf, hadd, genWindowDiscrepancy_point_mass _ hMpos hL', genWindowDiscrepancy_totient]
    ring

/-- The doubling rung, spelled out: at `p = 2` half the lifted cell's data is inherited
(`diagWindow_inter_two`, `blockSum_two_mul_congr_diag`) and the certificate below is
*still* compatible with every value of the cell above. -/
theorem double_rung_value_unconstrained {H L L' : ℕ} (hH : 0 < H) (hL : L ≤ H)
    (hL' : 0 < L') (v : ℤ) :
    ∃ f : ℕ → ℤ,
      (∀ n ∈ diagWindow H L, f n = (Nat.totient n : ℤ)) ∧
      (genCertifiedKill f H H L ↔ certifiedKill H H L) ∧
      genWindowDiscrepancy f (2 * H) (2 * H) L' = v :=
  rung_value_unconstrained (p := 2) le_rfl hH hL hL' v

end InduceLaw
end Lift
end ErdosProblems
