import Mathlib
import ErdosProblems.Erdos243.PrimitiveRecordBarrier

/-!
# Erdős 243: protected-epoch energy from reusable odd-prime barriers

`PrimitiveRecordBarrier` ends with an explicit open target:

> `-- OPEN: the quantitative record-excess obligation (r07 Theorem 8).`

That comment is discharged here, in the sharper form supplied by the return r02
(Lemma 2, "reusable odd-prime barriers").  The difference between r07 Theorem 8
and the statement proved below is the whole point of the r02 route:

* r07 charged one protected prime power against **one** barrier height, so a
  quantitative excess needed a fresh modulus per barrier, i.e. a CRT product of
  moduli whose size was never controlled.
* r02 charges **one** protected odd prime power `Q = p ^ l` against the *whole
  family* of odd multiples of `p` in the window `(pQ/4, pQ/2]`, of which there
  are at least `(Q - 8) / 8`.  No product of moduli appears anywhere.  A single
  divisibility `Q ∣ v s` is reused across `≈ Q / 8` independent barriers.

## What is proved

`protected_epoch_energy_integer` takes the orbit hypotheses of `odd_record_cut`
(dynamic cancellation with an arbitrary factor `hc n`, plus the centring bound
`2 * w n ≤ 3 * u n`), a protected odd prime power `Q = p ^ l ∣ v s` with
`16 ≤ Q` and `4 * runningMax u s < p * Q`, and any index `τ > s` with
`p * Q ≤ 2 * u τ`.  It returns a finite set `J` of *charged steps* in `[s, τ)`
such that

* every `n ∈ J` is a global record step (`runningMax u n < u (n + 1)`),
* every `n ∈ J` is cancellation-free (`hc n = 1`),
* every `n ∈ J` jumps by at least three (`u n + 3 ≤ u (n + 1)`), and
* with `K = |J|` and `X = ∑_{n ∈ J} (u (n+1) - u n - 2)`,
  `p * Q ≤ (8 * p + 8) * K + 4 * X + 8 * p`.

This is r02 (16) in integer form.  Divided through by `p` it says that a single
protected epoch forces record energy of order `Q / 8` — a per-epoch *lower*
bound on `K + X / p`, uniform in the cancellation factors.

The three structural ingredients are separated as reusable lemmas:

1. `barrierIdx_card_lower` — the barrier count `8 * |ℋ| + 8 ≥ Q` (counting the
   odd integers in `(Q/4, Q/2]`).
2. `fibre_card_le_spacing` — the per-step capacity `2 * p * k_n ≤ 2 * p + d_n`,
   because barriers first crossed at the same step lie in `(u n, u (n+1)]` and
   are spaced `2 * p` apart.
3. The per-barrier clean-record statement, proved inline inside the main
   theorem from `protectedPrimePower_persists` plus the odd-cut one-step
   argument of `odd_record_cut`: protection through the crossing gives
   `p ∣ v (n+1)`, which kills the landing `u (n+1) = b`, and a jump of at most
   two would force the pair `(b - 1, b + 1)`, both even, against adjacent
   coprimality.

## Sharpening of the return

The return states `τ` as the *first* index with `p * Q ≤ 2 * u τ`.  That
minimality is not used: the proof only needs some index `τ > s` at which the
orbit has reached `pQ/2`, because each barrier supplies its own first-crossing
index via `sInf`, and that index is automatically `< τ`.  The hypothesis
`∀ k, s ≤ k → k < τ → 2 * u k < p * Q` is therefore dropped, which strictly
strengthens the statement.

## Fixture

The three-step fixture behind the r02 window, with `(u₀, v₀) = (19, 1792818711)`
and `a₀ = 94358881`:

| step | `u n` | `e n` | `hc n` | `u (n+1)` |
|---|---|---|---|---|
| 0 | 19 | −9 | 1 | 28 |
| 1 | 28 | −9 | 1 | 37 |
| 2 | 37 | −9 | 1 | 46 |

Here `27 ∣ v₀`, so `p = 3`, `l = 3`, `Q = 27`, `p * Q = 81`, and the barrier
window `(81/4, 81/2] = (20.25, 40.5]` contains the four odd multiples of `3`
given by `barrierIdx 27 = Finset.Icc 3 6`, namely `21, 27, 33, 39`.  The first
step already crosses **two** of them (`19 < 21 ≤ 28` and `19 < 27 ≤ 28`), which
is exactly the situation the per-step capacity bound `2 * p * k_n ≤ 2 * p + d_n`
has to allow.  The raw numerator is `a₀ * u₀ - v₀ = 28`, and `28` is coprime to
`a₀ ^ 2`, so the step is cancellation-free.  These are recorded as `example`s
below.

## Claim ceiling

What is proved is a *lower* bound on the record energy inside one protected
epoch.  The matching *upper* bound — that a bounded-negative-part / summable
orbit has finite total energy, so that infinitely many protected epochs are
impossible — is not proved here and is exactly the open parent.  Nothing in
this module resolves Erdős #243, which remains open.  There is no `sorry`; the
one unformalised bridge is recorded as an `-- OPEN:` comment at the end.
-/

namespace ErdosProblems.Erdos243

/-! ## 1. The barrier family

`ℋ` is the set of odd multiples of `p` in `(p * Q / 4, p * Q / 2]`.  Because
`p * Q` is odd, neither endpoint is an integer multiple of `p`, so it is
cleanest to index the family by the odd number `2 * k + 1` and carry the two
window conditions in doubled form: `Q < 4 * (2 * k + 1)` and
`2 * (2 * k + 1) ≤ Q`.  The barrier itself is `(2 * k + 1) * p`.

The explicit interval below is contained in the exact index set (it is exactly
it when `Q ≡ 3 mod 8`, as for `Q = 27`), and is already large enough for the
counting bound. -/

/-- Index set of the barrier family: `k` indexes the barrier `(2 * k + 1) * p`
lying in the window `(p * Q / 4, p * Q / 2]`. -/
def barrierIdx (Q : ℕ) : Finset ℕ := Finset.Icc ((Q + 4) / 8) ((Q - 2) / 4)

/-- Every index in `barrierIdx Q` puts its barrier strictly above `p * Q / 4`
and at or below `p * Q / 2`, in doubled integer form. -/
theorem barrierIdx_spec {Q k : ℕ} (hQ : 16 ≤ Q) (hk : k ∈ barrierIdx Q) :
    Q < 4 * (2 * k + 1) ∧ 2 * (2 * k + 1) ≤ Q := by
  simp only [barrierIdx, Finset.mem_Icc] at hk
  omega

/-- **Barrier count.**  The window `(Q/4, Q/2]` contains at least `(Q - 8) / 8`
odd integers.  This is the "one protected prime power, many barriers" input:
the number of barriers grows linearly in `Q`. -/
theorem barrierIdx_card_lower {Q : ℕ} (hQ : 16 ≤ Q) :
    Q ≤ 8 * (barrierIdx Q).card + 8 := by
  simp only [barrierIdx, Nat.card_Icc]
  omega

/-! ## 2. Per-step capacity

Barriers first crossed at the same step all lie in the interval
`(u n, u (n + 1)]`, and distinct barriers differ by at least `2 * p`.  Hence a
step of jump `d` can be charged by at most `1 + d / (2 * p)` barriers. -/

/-- **Spacing bound.**  If every member of `F` indexes an odd multiple
`(2 * k + 1) * p` lying in `(x, y]`, then `2 * p * |F| ≤ 2 * p + (y - x)`. -/
theorem fibre_card_le_spacing {p x y : ℕ} (F : Finset ℕ)
    (hF : ∀ k ∈ F, x < (2 * k + 1) * p ∧ (2 * k + 1) * p ≤ y) :
    2 * p * F.card ≤ 2 * p + (y - x) := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hk0 : F.min' hne ∈ F := F.min'_mem hne
    have hk1 : F.max' hne ∈ F := F.max'_mem hne
    have hle : F.min' hne ≤ F.max' hne := F.min'_le _ hk1
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    have hsub : F ⊆ Finset.Icc (F.min' hne) (F.max' hne) := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨F.min'_le k hk, F.le_max' k hk⟩
    have hcard : F.card ≤ m + 1 := by
      have h := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h
      omega
    have hx := (hF _ hk0).1
    have hy := (hF _ hk1).2
    have hexp : (2 * F.max' hne + 1) * p = (2 * F.min' hne + 1) * p + 2 * p * m := by
      rw [hm]; ring
    have h5 : 2 * p * m + x ≤ y := by
      calc 2 * p * m + x ≤ 2 * p * m + (2 * F.min' hne + 1) * p :=
            Nat.add_le_add_left (le_of_lt hx) _
        _ = (2 * F.max' hne + 1) * p := by rw [hexp]; ring
        _ ≤ y := hy
    calc 2 * p * F.card ≤ 2 * p * (m + 1) := Nat.mul_le_mul (le_refl (2 * p)) hcard
      _ = 2 * p * m + 2 * p := by ring
      _ ≤ (y - x) + 2 * p := Nat.add_le_add_right (Nat.le_sub_of_add_le h5) _
      _ = 2 * p + (y - x) := by ring

/-! ## 3. The protected-epoch energy inequality (r02 Lemma 2 / r02 (16))

This closes the `-- OPEN:` target of `PrimitiveRecordBarrier`. -/

/-- **Protected-epoch energy, integer form.**

Along a dynamically reduced primitive orbit with *arbitrary* cancellation
satisfying the centring bound `2 * w n ≤ 3 * u n` from index `s`, suppose a
single odd prime power `Q = p ^ l` divides `v s`, with `16 ≤ Q`, the running
maximum still below `p * Q / 4`, and the orbit reaching `p * Q / 2` at some
index `τ > s`.  Then there is a set `J` of charged steps in `[s, τ)`, each of
which is a global record, cancellation-free, and jumps by at least three, whose
count `K` and excess `X = ∑ (d_n - 2)` satisfy

`p * Q ≤ (8 * p + 8) * K + 4 * X + 8 * p`.

The whole of `J` is charged against the *one* divisibility `Q ∣ v s`: the
barriers are the `≈ Q / 8` odd multiples of `p` in `(p * Q / 4, p * Q / 2]`,
all of them protected by the same prime power. -/
theorem protected_epoch_energy_integer
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ) :
    ∃ J : Finset ℕ,
      (∀ n ∈ J, s ≤ n ∧ n < τ ∧ runningMax u n < u (n + 1) ∧
          u n + 3 ≤ u (n + 1) ∧ hc n = 1) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by
  classical
  -- Basic arithmetic on the protected modulus.
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    obtain ⟨j, hj⟩ := hpodd
    omega
  have hppos : 0 < p := by omega
  have hQodd : Odd (p ^ l) := hpodd.pow
  have hpQodd : Odd (p * p ^ l) := hpodd.mul hQodd
  have hbig : 3 * 16 ≤ p * p ^ l := Nat.mul_le_mul hp3 hQ
  have hpow : p ^ (l + 1) = p * p ^ l := by rw [pow_succ]; ring
  obtain ⟨M, hM⟩ := hpQodd
  -- Split off the crossing index.
  obtain ⟨t, rfl⟩ : ∃ t, τ = t + 1 := ⟨τ - 1, by omega⟩
  have hts : s ≤ t := by omega
  -- Every barrier is first crossed at a clean record step with jump ≥ 3.
  have key : ∀ k ∈ barrierIdx (p ^ l), ∃ n,
      s ≤ n ∧ n ≤ t ∧ u n < (2 * k + 1) * p ∧ (2 * k + 1) * p ≤ u (n + 1) ∧
        runningMax u n < u (n + 1) ∧ u n + 3 ≤ u (n + 1) ∧ hc n = 1 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := barrierIdx_spec hQ hk
    -- The barrier sits strictly inside the window `(p * Q / 4, p * Q / 2]`.
    have hb1 : p * p ^ l < 4 * ((2 * k + 1) * p) := by
      calc p * p ^ l = p ^ l * p := by ring
        _ < (4 * (2 * k + 1)) * p := mul_lt_mul_of_pos_right hk1 hppos
        _ = 4 * ((2 * k + 1) * p) := by ring
    have hb2 : 2 * ((2 * k + 1) * p) ≤ p * p ^ l := by
      calc 2 * ((2 * k + 1) * p) = (2 * (2 * k + 1)) * p := by ring
        _ ≤ p ^ l * p := Nat.mul_le_mul hk2 (le_refl p)
        _ = p * p ^ l := by ring
    have hbu : (2 * k + 1) * p ≤ u (t + 1) := by omega
    have hexists : ∃ n, n ∈ {m | s ≤ m ∧ (2 * k + 1) * p ≤ u (m + 1)} := ⟨t, hts, hbu⟩
    -- First crossing of this barrier, as a plain natural number.
    obtain ⟨n, hns, hnb, hnt, hnmin⟩ :
        ∃ n, s ≤ n ∧ (2 * k + 1) * p ≤ u (n + 1) ∧ n ≤ t ∧
          ∀ i, i < n → s ≤ i → u (i + 1) < (2 * k + 1) * p := by
      refine ⟨sInf {m | s ≤ m ∧ (2 * k + 1) * p ≤ u (m + 1)},
        (Nat.sInf_mem hexists).1, (Nat.sInf_mem hexists).2, Nat.sInf_le ⟨hts, hbu⟩, ?_⟩
      intro i hi his
      by_contra hcon
      have hle : sInf {m | s ≤ m ∧ (2 * k + 1) * p ≤ u (m + 1)} ≤ i :=
        Nat.sInf_le ⟨his, by omega⟩
      omega
    -- Nothing in the window has reached the barrier yet.
    have hbefore : ∀ j, s ≤ j → j ≤ n → u j < (2 * k + 1) * p := by
      intro j hj hjn
      rcases Nat.lt_or_ge s j with hlt | hge
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        exact hnmin i (by omega) (by omega)
      · have h1 : u j ≤ runningMax u s := le_runningMax u hge
        omega
    have hun : u n < (2 * k + 1) * p := hbefore n hns (le_refl n)
    have hrun : runningMax u n < (2 * k + 1) * p := by
      refine runningMax_lt u (fun j hj => ?_)
      rcases Nat.lt_or_ge j s with hjs | hjs
      · have h1 : u j ≤ runningMax u s := le_runningMax u (le_of_lt hjs)
        omega
      · exact hbefore j hjs hj
    -- The protected prime power survives to the crossing.
    have hprotn : p ^ l ∣ v (n + 1) := by
      refine protectedPrimePower_persists a u v w hc p l s (M + 1) hp hred hvpos hw hwpos
        hnum hden hslow ?_ hprot (n + 1) (by omega) ?_
      · rw [hpow]; omega
      · intro j hj hjn1
        have hjb := hbefore j hj (by omega)
        omega
    have hpv : p ∣ v (n + 1) := dvd_trans (dvd_pow_self p (by omega)) hprotn
    -- Landing exactly on the barrier is impossible.
    have hne : u (n + 1) ≠ (2 * k + 1) * p := by
      intro hEq
      have hpu : p ∣ u (n + 1) := ⟨2 * k + 1, by rw [hEq]; ring⟩
      have hg : p ∣ Nat.gcd (u (n + 1)) (v (n + 1)) := Nat.dvd_gcd hpu hpv
      rw [(hred (n + 1) (by omega)).gcd_eq_one] at hg
      have := Nat.le_of_dvd Nat.one_pos hg
      omega
    -- Adjacent reduced numerators are coprime.
    have hcopnum : Nat.Coprime (u n) (u (n + 1)) := by
      have h1 : Nat.Coprime (u n) (w n) :=
        rawNext_coprime_currentNumerator (hred n hns) (hw n hns)
      exact h1.coprime_dvd_right ⟨hc n, by rw [hnum n hns]; ring⟩
    -- A jump of at most two would force `(b - 1, b + 1)`, both even.
    have hjump : u n + 3 ≤ u (n + 1) := by
      by_contra hcon
      have hB1 : (2 * k + 1) * p = u n + 1 := by omega
      have hodd1 : Odd (2 * k + 1) := ⟨k, by ring⟩
      have hBodd : Odd ((2 * k + 1) * p) := hodd1.mul hpodd
      obtain ⟨j, hj⟩ := hBodd
      have h2 : 2 ∣ Nat.gcd (u n) (u (n + 1)) :=
        Nat.dvd_gcd ⟨j, by omega⟩ ⟨j + 1, by omega⟩
      rw [hcopnum.gcd_eq_one] at h2
      omega
    -- A strict rise under the centring bound is cancellation-free.
    have hhcpos : 0 < hc n := by
      rcases Nat.eq_zero_or_pos (hc n) with h0 | hpos
      · exfalso
        have h1 := hnum n hns
        rw [h0, Nat.zero_mul] at h1
        have := hwpos n hns
        omega
      · exact hpos
    have hhclt : hc n < 2 := by
      by_contra hcon
      have hcon2 : 2 ≤ hc n := by omega
      have hmul : 2 * u (n + 1) ≤ hc n * u (n + 1) :=
        Nat.mul_le_mul hcon2 (le_refl (u (n + 1)))
      have h1 := hnum n hns
      have h2 := hslow n hns
      omega
    exact ⟨n, hns, hnt, hun, hnb, by omega, hjump, by omega⟩
  choose! f hf using key
  obtain ⟨J, hJdef⟩ : ∃ J : Finset ℕ, J = (barrierIdx (p ^ l)).image f := ⟨_, rfl⟩
  have hmemJ : ∀ k ∈ barrierIdx (p ^ l), f k ∈ J := by
    intro k hk
    rw [hJdef]
    exact Finset.mem_image_of_mem f hk
  have hJmem : ∀ n ∈ J, ∃ k ∈ barrierIdx (p ^ l), f k = n := by
    intro n hn
    rw [hJdef, Finset.mem_image] at hn
    exact hn
  refine ⟨J, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, hk, rfl⟩ := hJmem n hn
    obtain ⟨h1, h2, _, _, h5, h6, h7⟩ := hf k hk
    exact ⟨h1, by omega, h5, h6, h7⟩
  · -- Count the barriers fibrewise over their first-crossing steps.
    have hfib : (barrierIdx (p ^ l)).card
        = ∑ n ∈ J, ((barrierIdx (p ^ l)).filter (fun k => f k = n)).card :=
      Finset.card_eq_sum_card_fiberwise hmemJ
    have hspace : ∀ n ∈ J,
        2 * p * ((barrierIdx (p ^ l)).filter (fun k => f k = n)).card
          ≤ 2 * p + (u (n + 1) - u n) := by
      intro n _
      refine fibre_card_le_spacing _ (fun k hk => ?_)
      rw [Finset.mem_filter] at hk
      obtain ⟨hkS, hkf⟩ := hk
      obtain ⟨_, _, h3, h4, _, _, _⟩ := hf k hkS
      rw [hkf] at h3 h4
      exact ⟨h3, h4⟩
    have hsum1 : 2 * p * (barrierIdx (p ^ l)).card
        ≤ ∑ n ∈ J, (2 * p + (u (n + 1) - u n)) := by
      rw [hfib, Finset.mul_sum]
      exact Finset.sum_le_sum hspace
    have hd : ∀ n ∈ J, 2 * p + (u (n + 1) - u n)
        = (2 * p + 2) + (u (n + 1) - u n - 2) := by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := hJmem n hn
      obtain ⟨_, _, _, _, _, h6, _⟩ := hf k hk
      omega
    have hsum2 : ∑ n ∈ J, (2 * p + (u (n + 1) - u n))
        = (2 * p + 2) * J.card + ∑ n ∈ J, (u (n + 1) - u n - 2) := by
      calc ∑ n ∈ J, (2 * p + (u (n + 1) - u n))
          = ∑ n ∈ J, ((2 * p + 2) + (u (n + 1) - u n - 2)) := Finset.sum_congr rfl hd
        _ = (∑ _n ∈ J, (2 * p + 2)) + ∑ n ∈ J, (u (n + 1) - u n - 2) :=
            Finset.sum_add_distrib
        _ = (2 * p + 2) * J.card + ∑ n ∈ J, (u (n + 1) - u n - 2) := by
            rw [Finset.sum_const, smul_eq_mul]; ring
    have hA : p ^ l ≤ 8 * (barrierIdx (p ^ l)).card + 8 := barrierIdx_card_lower hQ
    have hBd : 2 * p * (barrierIdx (p ^ l)).card
        ≤ (2 * p + 2) * J.card + ∑ n ∈ J, (u (n + 1) - u n - 2) := by
      rw [← hsum2]; exact hsum1
    calc p * p ^ l ≤ p * (8 * (barrierIdx (p ^ l)).card + 8) :=
          Nat.mul_le_mul (le_refl p) hA
      _ = 4 * (2 * p * (barrierIdx (p ^ l)).card) + 8 * p := by ring
      _ ≤ 4 * ((2 * p + 2) * J.card + ∑ n ∈ J, (u (n + 1) - u n - 2)) + 8 * p :=
          Nat.add_le_add_right (Nat.mul_le_mul (le_refl 4) hBd) _
      _ = (8 * p + 8) * J.card + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p := by ring

/-! ## 4. The r02 fixture

`(u₀, v₀) = (19, 1792818711)`, `a₀ = 94358881`, protected modulus `27 = 3 ^ 3`.
The first step is `19 → 28` with `hc₀ = 1`, and it crosses two of the four
barriers at once. -/

example : (27 : ℕ) ∣ 1792818711 := ⟨66400693, by norm_num⟩

example : 94358881 * 19 - 1792818711 = 28 := by norm_num

/-- The first step is cancellation-free: `Nat.gcd w (a * v) = Nat.gcd w (a ^ 2)`
by `rawNext_gcd_eq_gcd_sq`, and `28` is coprime to `a₀ ^ 2`. -/
example : Nat.Coprime 28 (94358881 ^ 2) := Nat.Coprime.pow_right 2 (by norm_num)

example : barrierIdx 27 = Finset.Icc 3 6 := by norm_num [barrierIdx]

example : (barrierIdx 27).card = 4 := by norm_num [barrierIdx, Nat.card_Icc]

/-- The four barriers of the fixture window `(81/4, 81/2]`. -/
example : (2 * 3 + 1) * 3 = 21 ∧ (2 * 4 + 1) * 3 = 27 ∧ (2 * 5 + 1) * 3 = 33 ∧
    (2 * 6 + 1) * 3 = 39 := by norm_num

/-- The first jump `19 → 28` charges two barriers, so the per-step capacity
bound must allow `k_n > 1`; this is why `fibre_card_le_spacing` is stated with
the `2 * p` slack term. -/
example : 19 < 21 ∧ 21 ≤ 28 ∧ 19 < 27 ∧ 27 ≤ 28 := by norm_num

/-!
## What remains open

`protected_epoch_energy_integer` is fully proved from its hypotheses; there is
no `sorry` and no admitted lemma.  It is a *lower* bound on the record energy
of one protected epoch.

-- OPEN: the matching upper bound.  Statement: for a dynamically reduced
-- primitive orbit with bounded negative part (equivalently, with the
-- normalised vanishing hypothesis `hvanish` of
-- `recordRiseTwo_sylvesterNext_eventually`), the total record energy
--   `∑_{n record step} (1 / Real.sqrt (u n) + (u (n+1) - u n - 2) / u n)`
-- is finite.  Combined with an infinite supply of protected epochs whose
-- moduli `Q` tend to infinity, the energy inequality proved here would force a
-- contradiction and hence close the record-jump route.  The supply of epochs is
-- the same analytic bridge already recorded as `hsupply` in
-- `PrimitiveRecordBarrier`; the finiteness of the energy is a genuinely new
-- obligation and is not formalised anywhere in this corpus.

Erdős #243 is not resolved by this module.
-/

end ErdosProblems.Erdos243
