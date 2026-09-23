# Formal evidence: The Binary Totient Series, Section 12

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="lem-orbit"></a>

## Lemma 12.1 (The doubling identity), page 111

> *For all $`N\ge 0`$ and $`h\ge 1`$,
> ``` math
> R_{N+1}=2R_N-\varphi(N+1),
>   \qquad
>   R_{N+h}-R_N \;=\; 2^N\alpha_h-\bigl(\Phi_{N+h}-\Phi_N\bigr),
> ```
> so $`R_{N+h}-R_N \equiv 2^N\alpha_h \pmod 1`$, and consequently the exact first character of the tail difference is the $`\times 2`$ orbit of one real number:
> ``` math
> e(R_{N+h}-R_N)
>   \;=\; e\bigl(2^N\alpha_h\bigr),
>   \qquad e(x):=\exp(2\pi i x).
> ```
> Hence, for fixed $`h`$, the phases $`\{\,R_{N+h}-R_N \bmod 1\,\}_{N\ge 0}`$ are the forward orbit of $`\alpha_h \bmod 1`$ under $`x\mapsto 2x`$.*

The Lean declarations below together state a result at least as strong as this one. The Lean statements give the recurrence, the identity for $R_{N+h}-R_N$, the congruence modulo $1$, the equality of first characters and the description of the phases as the doubling orbit of $\alpha_h$, with $\alpha_h=(2^h-1)S$ written out. They also hold at $h=0$, where $\alpha_0=0$ and every identity is trivial.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_recurrence`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L26)

```lean
theorem orbit_tail_recurrence (N : ℕ) :
    totientTail (N + 1) = 2 * totientTail N - (Nat.totient (N + 1) : ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L32)

```lean
theorem orbit_tail_diff_eq (h N : ℕ) :
    totientTail (N + h) - totientTail N
      = (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        - ((totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_sub_scaled_is_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L41)

```lean
theorem orbit_tail_diff_sub_scaled_is_int (h N : ℕ) :
    ∃ z : ℤ,
      totientTail (N + h) - totientTail N
          - (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        = (z : ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_firstChar_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L53)

```lean
theorem orbit_tail_diff_firstChar_eq (h N : ℕ) :
    Complex.exp
        (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) * Complex.I)
      = Complex.exp
        (((2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ℝ) : ℂ) * Complex.I)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_fract_eq_doubling_orbit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L75)

```lean
theorem orbit_tail_diff_fract_eq_doubling_orbit (h N : ℕ) :
    Int.fract (totientTail (N + h) - totientTail N)
      = Int.fract
          ((fun x : ℝ => 2 * x)^[N]
            (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)))
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.doublingMap_iterate_apply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L64)

```lean
theorem doublingMap_iterate_apply (α : ℝ) (N : ℕ) :
    (fun x : ℝ => 2 * x)^[N] α = 2 ^ N * α
```

<a id="lem-orbit-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `orbit_tail_recurrence` | [E249_27/Challenge.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L87) | [PaperStatementsAU.lean, line 299](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L299) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `orbit_tail_diff_eq` | [E249_27/Challenge.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L58) | [PaperStatementsAU.lean, line 274](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L274) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `orbit_tail_diff_sub_scaled_is_int` | [E249_27/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L80) | [PaperStatementsAU.lean, line 293](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L293) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `orbit_tail_diff_firstChar_eq` | [E249_27/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L64) | [PaperStatementsAU.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L279) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `orbit_tail_diff_fract_eq_doubling_orbit` | [E249_27/Challenge.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L73) | [PaperStatementsAU.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L287) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `doublingMap_iterate_apply` | [E249_27/Challenge.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L36) | [PaperStatementsAJ.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAJ.lean#L271) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-transfer"></a>

## Proposition 12.2 (Transfer to the doubling orbit), page 111

> *Suppose that
> ``` math
> \forall h\ge 1\ \forall X_0\ \exists X\ge \max(X_0,1):\quad
>   \sum_{N=X}^{2X-1}\cos\bigl(2\pi\,2^{N}\alpha_h\bigr)\;\le\;\tfrac{89}{100}\,X .
> ```
> This hypothesis implies that $`S`$ is irrational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_block_cosine_gap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L92)

```lean
theorem irrational_totientSeries_of_block_cosine_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))))
        ≤ (89 / 100 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-transfer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totientSeries_of_block_cosine_gap` | [E249_27/Challenge.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L40) | [PaperStatementsAJ.lean, line 412](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAJ.lean#L412) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-digitform"></a>

## Corollary 12.3 (A digit version of the analytic condition), page 112

> *Let $`\rho_h(X)`$ denote the proportion of $`N\in[X,2X)`$ with $`\|2^N\alpha_h\|_{\mathbb{R}/\mathbb{Z}}\ge 1/4`$. If for every $`h\ge 1`$ there are cofinally many $`X`$ with $`\rho_h(X)\ge 11/100`$, then $`S`$ is irrational. For nondyadic $`\alpha_h`$, the condition counted by $`\rho_h(X)`$ is exactly a change between binary digits $`N+1`$ and $`N+2`$. Thus the same sufficient hypothesis asks for at least $`11X/100`$ such changes, counted with $`X\le N<2X`$, on arbitrarily large blocks for every $`h`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_proportion`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L121)

```lean
theorem irrational_totientSeries_of_quarterFarPhase_proportion
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) ≤ quarterFarPhaseProportion h X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_binaryDigitAt_change`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L146)

```lean
theorem quarterFarFromInt_iff_binaryDigitAt_change {α : ℝ} (hnd : NotDyadicRational α) (N : ℕ) :
    QuarterFarFromInt ((2 : ℝ) ^ N * α) ↔ binaryDigitAt α (N + 1) ≠ binaryDigitAt α (N + 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_digitChange_count`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L233)

```lean
theorem irrational_totientSeries_of_digitChange_count
    (hnd : ∀ h : ℕ, 1 ≤ h → NotDyadicRational (totientAlphaShift h))
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤
        ((((Finset.Ico X (2 * X)).filter
            fun N => binaryDigitAt (totientAlphaShift h) (N + 1)
              ≠ binaryDigitAt (totientAlphaShift h) (N + 2)).card : ℕ) : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_count`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L95)

```lean
theorem irrational_totientSeries_of_quarterFarPhase_count
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤ (quarterFarPhaseCount h X : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_floor_bounds`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L45)

```lean
theorem quarterFarFromInt_iff_floor_bounds (x : ℝ) :
    QuarterFarFromInt x ↔ (1 / 4 : ℝ) ≤ x - (⌊x⌋ : ℝ) ∧ x - (⌊x⌋ : ℝ) ≤ 3 / 4
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.cos_nonpos_of_quarterFarFromInt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L70)

```lean
theorem cos_nonpos_of_quarterFarFromInt {x : ℝ} (hx : QuarterFarFromInt x) :
    Real.cos (2 * Real.pi * x) ≤ 0
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.tailOrbitFirstExp_re_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L81)

```lean
theorem tailOrbitFirstExp_re_eq (h N : ℕ) :
    (tailOrbitFirstExp h N).re = Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * totientAlphaShift h))
```

<a id="cor-digitform-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totientSeries_of_quarterFarPhase_proportion` | [E249_27/Challenge.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L127) | [PaperStatementsAM.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L34) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `quarterFarFromInt_iff_binaryDigitAt_change` | [E249_27/Challenge.lean, line 133](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L133) | [PaperStatementsAM.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L39) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `irrational_totientSeries_of_digitChange_count` | [E249_27/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L111) | [PaperStatementsAM.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L20) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `irrational_totientSeries_of_quarterFarPhase_count` | [E249_27/Challenge.lean, line 121](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L121) | [PaperStatementsAM.lean, line 29](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L29) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `quarterFarFromInt_iff_floor_bounds` | [E249_27/Challenge.lean, line 137](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L137) | [PaperStatementsAM.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L43) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `cos_nonpos_of_quarterFarFromInt` | [E249_27/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L107) | [PaperStatementsAM.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L17) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `tailOrbitFirstExp_re_eq` | [E249_27/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L152) | [PaperStatementsBL.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsBL.lean#L20) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-lacunary"></a>

## Theorem 12.5 (The block norm condition is stronger in the class $`0\le c(n)\le n`$), page 114

> *Let $`c(n)=1`$ if $`n=k!`$ for some $`k\ge 1`$ and $`c(n)=0`$ otherwise, so $`0\le c(n)\le n`$ for all $`n\ge 1`$, and let $`\beta=\sum_{n\ge1}c(n)/2^{n}
> =\sum_{k\ge 1}2^{-k!}`$. Then $`\beta`$ is irrational, and for every $`h\ge 1`$ and every $`X\ge 81(h+5)`$,
> ``` math
> \sum_{N=X}^{2X-1}\cos\bigl(2\pi\,2^{N}(2^{h}-1)\beta\bigr) \;>\; \tfrac{9}{10}X .
> ```
> Consequently the block norm condition fails for $`\beta`$ at every sufficiently large scale, for every admissible truncation depth, even though $`\beta`$ is irrational. Thus irrationality, nonnegative integer coefficients and the bound $`c(n)\le n`$ do not imply the block gap. A proof for $`S`$ needs an additional property not shared by this example; the comparison does not specify which additional property will suffice.*

The Lean declarations below together state a result at least as strong as this one. The Lean statements have the same hypotheses and conclusions as the printed claims. The failure of the block norm condition is stated as $\bigl\|\sum_{X\le N<2X}E(h,N,L)\bigr\|>\tfrac{21}{25}X$ for every $h\ge1$, every $X\ge81(h+5)$ and every depth $L$ with $16(2X+h+L+2)\le2^L$, where $E$ is formed from the coefficients $c(n)$.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.lacCoef_bounds`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L68)

```lean
theorem lacCoef_bounds {n : ℕ} (hn : 1 ≤ n) : 0 ≤ lacCoef n ∧ lacCoef n ≤ (n : ℤ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.lacBeta_eq_factorial_series`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L88)

```lean
theorem lacBeta_eq_factorial_series : lacBeta = ∑' k : ℕ, (1 : ℝ) / 2 ^ ((k + 1)!)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_lacBeta`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L121)

```lean
theorem irrational_lacBeta : Irrational lacBeta
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_cos_gap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L333)

```lean
theorem lacunary_block_cos_gap {h X : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X) :
    (9 / 10 : ℝ) * X
      < ∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta))
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_norm_fails`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L587)

```lean
theorem lacunary_block_norm_fails {h X L : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) :
    (21 / 25 : ℝ) * X < ‖∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L‖
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.cos_pi_div_eight_gt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L317)

```lean
theorem cos_pi_div_eight_gt : (9238 / 10000 : ℝ) < Real.cos (Real.pi / 8)
```

<a id="thm-lacunary-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lacCoef_bounds` | [E249_27/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L184) | [PaperStatementsAN.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L23) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `lacBeta_eq_factorial_series` | [E249_27/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L181) | [PaperStatementsAN.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L21) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `irrational_lacBeta` | [E249_27/Challenge.lean, line 178](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L178) | [PaperStatementsAN.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L19) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `lacunary_block_cos_gap` | [E249_27/Challenge.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L187) | [PaperStatementsAN.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L25) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `lacunary_block_norm_fails` | [E249_27/Challenge.lean, line 193](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L193) | [PaperStatementsAN.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L30) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `cos_pi_div_eight_gt` | [E249_27/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L175) | [PaperStatementsAN.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L17) | [E249_27](../../evidence/comparator/replay-35882032091/receipt-E249_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-dickman"></a>

## Proposition 12.6 (A one-sided bound for the unassigned terms), page 116

> *Fix $`h,s`$ and choose the admissible depth $`L`$ minimally for each large $`X`$. Put $`t=L-s+1=O_{h,s}(\log X)`$ and $`y_X=4\sqrt X+2t/\sqrt X`$. If $`n=N+t`$ is unassigned, then its largest prime factor satisfies $`P(n)\le y_X`$. Consequently
> ``` math
> \begin{aligned}
>  \#\{N\in[X,2X):N\notin\mathcal A\}
>  &\le \Psi(2X+t-1,y_X)-\Psi(X+t-1,y_X)\\
>  &=\bigl(1-\log2+o(1)\bigr)X<\tfrac8{25}X
> \end{aligned}
> ```
> for all sufficiently large $`X`$. Here $`\Psi(x,y)`$ counts the positive integers at most $`x`$ whose prime factors are all at most $`y`$. This is an upper bound for the unassigned count, not an asymptotic equality for that count.*

The Lean declaration below states a result at least as strong as this one. The Lean statement gives the explicit bound $t\le h+\lfloor\log_2X\rfloor+11$ in place of $t=O_{h,s}(\log X)$, and proves the bound $P(n)\le y_X$ and the bound of the unassigned count by $\Psi(2X+t-1,y_X)-\Psi(X+t-1,y_X)$ for every $X\ge1$; the asymptotic $(1-\log2+o(1))X$ and the bound $\tfrac8{25}X$ for all large $X$ are as printed.

[`ErdosProblems.Erdos249.PaperCompleteR21.prop_dickman`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/UnassignedSmoothCount.lean#L556)

```lean
theorem prop_dickman (h s : ℕ) :
    (∀ X, AdmissibleDepth h s X (minimalDepth h s X) ∧
        ∀ L, AdmissibleDepth h s X L → minimalDepth h s X ≤ L) ∧
    (∀ X, minimalOffset h s X ≤ h + Nat.log 2 X + 11) ∧
    (∀ X N, 0 < X → N ∈ Ico X (2 * X) → N ∉ pivotSupplierBases X (minimalDepth h s X) s →
      ∀ hn : 1 < N + minimalOffset h s X,
        (((N + minimalOffset h s X).primeFactors.max'
            (Nat.nonempty_primeFactors.mpr hn) : ℕ) : ℝ) ≤ minimalCut h s X) ∧
    (∀ X, 0 < X →
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        ≤ (smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) ∧
    Tendsto (fun X : ℕ =>
        ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) / X)
      atTop (𝓝 (1 - Real.log 2)) ∧
    (∀ᶠ X : ℕ in atTop,
      ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) < 8 / 25 * X ∧
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        < 8 / 25 * X)
```

<a id="prop-dickman-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `prop_dickman` | [E249_28/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_28/Challenge.lean#L96) | [PaperStructuresQ.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_28/PaperStructuresQ.lean#L20) | [E249_28](../../evidence/comparator/replay-35882032091/receipt-E249_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-badcof"></a>

## Proposition 12.7 (The excluded-cofactor estimate), page 117

> *Fix $`h,s`$ and use the minimal admissible depth $`L`$, as in Proposition <a href="#prop:dickman" data-reference-type="ref" data-reference="prop:dickman">276</a>; thus $`t=L-s+1=O_{h,s}(\log X)`$. For $`\eta\in(0,1)`$ let $`B(\eta)=\{m\ge1:\varphi(m)<\eta m\}`$, with natural density $`D(\eta)`$; by Schoenberg’s theorem $`D`$ exists, is continuous, and $`D(0+)=0`$ \[schoenberg1928, §17, p. 193\], in the framework of \[schoenberg1936, Theorem 1, pp. 318–319, and §8, p. 323\] <span class="sans-serif">\[Cited\]</span>. Then
> ``` math
> \#\{N\in\mathcal A:m_N\in B(\eta)\}
>   \;\le\;\bigl(D(\eta)+o(1)\bigr)X ,
> ```
> so a single choice of $`\eta`$ with $`D(\eta)<1/200`$ meets the $`\tfrac{1}{100}X`$ budget for all large $`X`$. This choice fixes $`\eta`$ before $`X_0`$, as required. It supplies only the excluded-cofactor bound: the mean and mean-subtracted estimates must still hold for this same $`\eta`$, and do not follow from making $`\eta`$ smaller.*

The Lean proof assumes the prime number theorem. Lean takes this input as a hypothesis (`PrimeNumberTheorem`); it is not proved in Lean.

[`ErdosProblems.Erdos249.PaperCompleteR21.prop_badcof`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExcludedCofactorEstimate.lean#L654)

```lean
theorem prop_badcof (hPNT : ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem)
    (h s : ℕ) (η D : ℝ) (hD : HasNaturalDensity (excludedCofactorSet η) D) :
    (∀ X : ℕ, minimalOffset h s X ≤ h + Nat.log 2 X + 11) ∧
    (∀ X : ℕ, (pivotSupplierBases X (minimalDepth h s X) s).filter
        (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)
      = pivotBadBases X (minimalDepth h s X) s η) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        ≤ (D + ε) * X) ∧
    (D < 1 / 200 → ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        < (1 / 100 : ℝ) * X ∧
      ‖pivotBadContribution h X (minimalDepth h s X) s η‖ ≤ (1 / 100 : ℝ) * X)
```

The assumed input [`PrimeNumberTheorem`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L28) is

```lean
def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)
```

<a id="prop-badcof-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="prop-route4"></a>

## Proposition 12.9, page 121

> *$`\mathcal{C}(h,N,h)`$ holds whenever $`\bigl\|2^{N+h}S-2^{N}S\bigr\|_{\mathbb{R}/\mathbb{Z}}>2(N+2h+2)/2^{h}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_fullDepth_phase_separation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L130)

```lean
theorem certifiedKill_of_fullDepth_phase_separation (h N : ℕ)
    (hsep : ∀ k : ℤ,
      2 * ((N : ℝ) + 2 * h + 2) / 2 ^ h <
        |(2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
            - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (k : ℝ)|) :
    certifiedKill h N h
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.bracket_of_two_sided_separation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L119)

```lean
theorem bracket_of_two_sided_separation
    {c P m δ : ℝ} (_hc : 0 < c) (_hm0 : 0 ≤ m) (_hmP : m < P)
    (hδ : |δ| < c) (h1 : 2 * c < |m + δ|) (h2 : 2 * c < |m + δ - P|) :
    c < m ∧ m < P - c
```

<a id="prop-route4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `certifiedKill_of_fullDepth_phase_separation` | [E249_28/Challenge.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_28/Challenge.lean#L142) | [PaperStatementsAT.lean, line 343](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_28/PaperStatementsAT.lean#L343) | [E249_28](../../evidence/comparator/replay-35882032091/receipt-E249_28.json) |
| `bracket_of_two_sided_separation` | [E249_28/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_28/Challenge.lean#L124) | [PaperStatementsAJ.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_28/PaperStatementsAJ.lean#L157) | [E249_28](../../evidence/comparator/replay-35882032091/receipt-E249_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
