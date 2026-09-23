# Formal evidence: The Binary Totient Series, Section 10

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-rational-series-preserving-totient-parity"></a>

## Proposition 10.1, page 96

The Lean declarations below together state this result.

1. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_six`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L227)

```lean
theorem parityCoboundaryWeight_le_six (n : ℕ) :
    parityCoboundaryWeight n ≤ 6
```

2. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_self`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L155)

```lean
theorem parityCoboundaryWeight_le_self (n : ℕ) :
    parityCoboundaryWeight n ≤ n
```

3. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_mod_two_eq_totient`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L194)

```lean
theorem parityCoboundaryWeight_mod_two_eq_totient (n : ℕ) :
    parityCoboundaryWeight n % 2 = Nat.totient n % 2
```

4. [`Erdos249257.TotientParityCoboundaryCountermodel.exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L457)

```lean
theorem exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs
    (N G K : ℕ) :
    ∃ k : ℕ,
      N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        parityCoboundaryWeight (2 ^ (k + i + 3)) = 6 ∧
        parityCoboundaryWeight (2 ^ (k + i + 3) + 1) = 0
```

5. [`Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L359)

```lean
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2
```

<a id="prop-rational-series-preserving-totient-parity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `parityCoboundaryWeight_le_six` | [E249_26/Challenge.lean, line 138](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L138) | [PaperStatementsAG.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L42) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `parityCoboundaryWeight_le_self` | [E249_26/Challenge.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L134) | [PaperStatementsAG.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L39) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `parityCoboundaryWeight_mod_two_eq_totient` | [E249_26/Challenge.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L142) | [PaperStatementsAG.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L45) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs` | [E249_26/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L124) | [PaperStatementsAG.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L16) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `tsum_parityCoboundaryWeight_eq_three_halves` | [E249_02/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L65) | [PaperStatementsAG.lean, line 48](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAG.lean#L48) | [E249_02](../../evidence/comparator/replay-35882032091/receipt-E249_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-complement-divisibility-after-multiplication"></a>

## Lemma 10.2, page 98

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.complementDenominator_dvd_scalar`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ScalarLocalisationAndInversePhaseGauge.lean#L29)

```lean
theorem complementDenominator_dvd_scalar
    (x : ℚ) (c : ℤ) {H : ℕ} (_hHpos : 0 < H) (hH : H ∣ x.den)
    (hscaled : ((c : ℚ) * x).den ∣ H) :
    ((x.den / H : ℕ) : ℤ) ∣ c
```

<a id="lem-complement-divisibility-after-multiplication-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `complementDenominator_dvd_scalar` | [E249_26/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L149) | [PaperStatementsAJ.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAJ.lean#L168) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-nonvanishing-unique-largest-denominator-exponent"></a>

## Lemma 10.3, page 99

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_clearing`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L8)

```lean
theorem signed_dyadic_clearing {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α)
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (2 : ℚ) ^ e m * (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) =
      ((∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i) : ℤ) : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_sum_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L28)

```lean
theorem signed_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) ≠ 0
```

3. [`Erdos249257.SignedQMomentObstruction.scaled_dyadic_sum_odd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/SignedQMomentObstruction.lean#L78)

```lean
theorem scaled_dyadic_sum_odd {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) % 2 = 1
```

<a id="lem-nonvanishing-unique-largest-denominator-exponent-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `signed_dyadic_clearing` | [E249_05/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L117) | [PaperStatementsAE.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L145) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `signed_dyadic_sum_ne_zero` | [E249_05/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L124) | [PaperStatementsAE.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L152) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `scaled_dyadic_sum_odd` | [E249_06/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L81) | [PaperStatementsAF.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAF.lean#L30) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-nonzero-minor-survives-inverse-phase"></a>

## Proposition 10.4, page 100

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.inversePhaseGauge_locks_row_and_preserves_minor`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ScalarLocalisationAndInversePhaseGauge.lean#L51)

```lean
theorem inversePhaseGauge_locks_row_and_preserves_minor
    {d : ℕ} (_hd : 1 ≤ d) (e : Fin d → ℕ) (z : Fin d → ℂ)
    (hz : ∀ j, z j ≠ 0) (i₀ : Fin d) (hi₀ : e i₀ = 1) :
    (∀ j, (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)) i₀ j = 1) ∧
      Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹))
          = Matrix.det (phasePowerMatrix e z) * ∏ j, (z j)⁻¹ ∧
      (Matrix.det (phasePowerMatrix e z) ≠ 0 →
        Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)) ≠ 0) ∧
      ((∀ j, ‖z j‖ = 1) →
        ‖Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹))‖
          = ‖Matrix.det (phasePowerMatrix e z)‖)
```

<a id="prop-nonzero-minor-survives-inverse-phase-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `inversePhaseGauge_locks_row_and_preserves_minor` | [E249_26/Challenge.lean, line 164](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L164) | [PaperStatementsAY.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAY.lean#L94) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-tail-integrality-lcm-grid"></a>

## Proposition 10.5, page 100

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L8)

```lean
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-tail-integrality-lcm-grid-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcm_grid_flatness` | [E249_09/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L209) | [PaperStatementsAT.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L199) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-grid-certificate-gives-nonintegral"></a>

## Proposition 10.6, page 100

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L36)

```lean
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-finite-grid-certificate-gives-nonintegral-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperGridNumerator_eq` | [E249_09/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L287) | [PaperStatementsAX.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L238) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_grid_nonintegral_pair` | [E249_09/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L272) | [PaperStatementsAX.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L223) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-exact-dyadic-rank-infinite-dimensionality"></a>

## Theorem 10.7, page 101

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_entries`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L33)

```lean
theorem canonicalTotientKernelFamily_entries (e : ℕ) :
    canonicalTotientKernelFamily e (Sum.inl 0) = (fun n => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily e (Sum.inl 1)
        = (fun n => (Nat.totient (2 * n) : ℚ)) ∧
      ∀ (j : Fin e) (r : Fin (2 ^ j.val)),
        canonicalTotientKernelFamily e (Sum.inr ⟨j, r⟩)
          = fun n => (Nat.totient (2 ^ (j.val + 1) * n + (2 * r.val + 1)) : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_independent_card_and_span`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L53)

```lean
theorem canonicalTotientKernelFamily_independent_card_and_span (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Function.Injective (canonicalTotientKernelFamily e) ∧
      Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))
        = Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) ∧
      ¬ FiniteDimensional ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily))
```

<a id="thm-exact-dyadic-rank-infinite-dimensionality-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `canonicalTotientKernelFamily_entries` | [E249_25/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L260) | [PaperStatementsBB.lean, line 24](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L24) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `canonicalTotientKernelFamily_independent_card_and_span` | [E249_26/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L205) | [PaperStatementsBB.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsBB.lean#L27) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
