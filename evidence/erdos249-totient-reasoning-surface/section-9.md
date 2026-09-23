# Formal evidence: The Binary Totient Series, Section 9

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-hgap-real"></a>

## Theorem 9.4 (A real-part bound gives a certificate), page 84

> *For all $`h,X,L`$ with $`0<X`$ and the room condition $`16(2X{+}h{+}L{+}2)\le 2^L`$, if
> ``` math
> \sum_{N=X}^{2X-1} \operatorname{Re}E(h,N,L) \;\le\; \tfrac{9}{10}\,X ,
> ```
> then $`\exists N\in[X,2X)`$ with $`\mathcal{C}\ h\ N\ L`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.windowFirstCos_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L23)

```lean
theorem windowFirstCos_unfolded (h N L : ℕ) :
    windowFirstCos h N L
      = Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ)))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_real_part_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L34)

```lean
theorem exists_certifiedKill_of_block_real_part_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

<a id="thm-hgap-real-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `windowFirstCos_unfolded` | [E249_21/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L220) | [PaperStatementsAU.lean, line 572](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAU.lean#L572) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `exists_certifiedKill_of_block_real_part_bound` | [E249_21/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L175) | [PaperStatementsAT.lean, line 433](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L433) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-hgap-subset"></a>

## Theorem 9.5 (The same implication for a nonempty subset), page 84

> *For any nonempty finite $`T\subseteq\mathbb N`$ with $`T\subset[0,2X)`$ and the same room condition, if
> ``` math
> \sum_{N\in T} \operatorname{Re}E(h,N,L) \;\le\; \tfrac{9}{10}\,|T| ,
> ```
> then $`\exists N\in T`$ with $`\mathcal{C}\ h\ N\ L`$. This generalises Theorem 9.4: $`T`$ can be *any* explicitly chosen nonempty finite subset of the dyadic block, not the whole block, and the proof (an averaging pigeonhole) never uses that $`T`$ has positive density or comes from a partition.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_subset_real_part_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L50)

```lean
theorem exists_certifiedKill_of_subset_real_part_bound {h X L : ℕ}
    (T : Finset ℕ)
    (hTlt : ∀ N ∈ T, N < 2 * X)
    (hTne : T.Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ T,
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * T.card) :
    ∃ N ∈ T, certifiedKill h N L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.block_real_part_bound_of_subset_form`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L65)

```lean
theorem block_real_part_bound_of_subset_form {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

<a id="thm-hgap-subset-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_certifiedKill_of_subset_real_part_bound` | [E249_21/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L186) | [PaperStatementsAT.lean, line 443](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L443) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `block_real_part_bound_of_subset_form` | [E249_21/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L157) | [PaperStatementsAT.lean, line 319](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L319) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-hgap-norm"></a>

## Theorem 9.6 (A norm bound gives the real-part criterion), page 84

> *The complex norm bound implies the real-part bound ($`|z|\ge\mathrm{Re}(z)`$, and $`21/25 < 9/10`$ absorbs the slack), so it composes through Theorem 9.4 to the same certificate. Define
> ``` math
> \text{block norm condition} :\Leftrightarrow\;
>   \forall h{>}0\ \forall X_0\ \exists X, L,\ \max(X_0,1)\le X\ \wedge\ 16(2X{+}h{+}L{+}2)\le 2^L\ \wedge
> ```
> ``` math
> \Bigl\|\ \sum_{N=X}^{2X-1}E(h,N,L)\ \Bigr\| \;\le\; \tfrac{21}{25}\,X .
> ```
> This condition is unproved; it is the open target itself. Then
> ``` math
> \text{block norm condition} \;\Longrightarrow\; \mathrm{Irrational}\Bigl(\sum_{n\ge 0}
>   \tfrac{\varphi(n)}{2^n}\Bigr),
> ```
> proved in full, with no further gap, by chaining Theorem 9.6$`\to`$Theorem 9.4$`\to`$ Theorem 6.47.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.blockNormCondition_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L86)

```lean
theorem blockNormCondition_unfolded :
    DTWFirstHarmonicNormGap ↔
      ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
        max X₀ 1 ≤ X ∧
        16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
        ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.real_part_bound_of_norm_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L97)

```lean
theorem real_part_bound_of_norm_bound {h X L : ℕ} (hX : (0 : ℝ) ≤ X)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (21 / 25 : ℝ) < 9 / 10 ∧
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_norm_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L110)

```lean
theorem exists_certifiedKill_of_block_norm_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_blockNormCondition`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L118)

```lean
theorem irrational_of_blockNormCondition (hgap : DTWFirstHarmonicNormGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-hgap-norm-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `blockNormCondition_unfolded` | [E249_21/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L149) | [PaperStatementsAT.lean, line 312](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L312) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `real_part_bound_of_norm_bound` | [E249_21/Challenge.lean, line 214](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L214) | [PaperStatementsAU.lean, line 396](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAU.lean#L396) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `exists_certifiedKill_of_block_norm_bound` | [E249_21/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L168) | [PaperStatementsAT.lean, line 427](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L427) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `irrational_of_blockNormCondition` | [E249_21/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L199) | [PaperStatementsAT.lean, line 588](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L588) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-positivity-remaining-residue-inequality"></a>

## Theorem 9.10, page 85

> *For every $`a\ge 8`$ and every $`J`$ with $`J+(a{+}6) < 2\cdot 2^a`$,
> ``` math
> 0 \;<\; {R}(2H{+}J) - {R}(H{+}J), \qquad H={H}(2^a).
> ```
> Hence $`0 < \Omega_a`$ for every $`a\ge 8`$. The proof is genuinely uniform in $`a`$: it rests on two facts proved for all $`a\ge 8`$ and $`0<j<2^{a+1}`$, namely $`\delta_{2^a}(j)>0`$ and $`H<8\cdot 2^a\,\delta_{2^a}(j)`$, by a two-case structural split (divisor letter vs. foreign prime power), with absolute constants $`4,8,32`$ and no lookup table.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_corridor_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L39)

```lean
theorem actualLcm_corridor_pos {a : ℕ} (ha : 8 ≤ a) :
    (∀ J : ℕ, J + (a + 6) < 2 * 2 ^ a →
        0 < totientTail (2 * periodLcm (2 ^ a) + J)
              - totientTail (periodLcm (2 ^ a) + J)) ∧
      0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.corridor_letter_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L49)

```lean
theorem corridor_letter_pos {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    0 < lcmRayArithmeticLetter (2 ^ a) j
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.corridor_height_lt_letter`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L56)

```lean
theorem corridor_height_lt_letter {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    (periodLcm (2 ^ a) : ℤ) < 8 * (2 ^ a : ℤ) * lcmRayArithmeticLetter (2 ^ a) j
```

<a id="thm-positivity-remaining-residue-inequality-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `actualLcm_corridor_pos` | [E249_22/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L72) | [PaperStatementsAT.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAT.lean#L271) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `corridor_letter_pos` | [E249_22/Challenge.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L84) | [PaperStatementsAT.lean, line 351](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAT.lean#L351) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `corridor_height_lt_letter` | [E249_22/Challenge.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L79) | [PaperStatementsAT.lean, line 345](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAT.lean#L345) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-proved-implications"></a>

## Theorem 9.12 (The proved implications), page 86

> *For every $`a\ge 8`$ and every $`J,K,m`$ inside the sign corridor ($`J{+}K{+}(a{+}6) < 2\cdot 2^a`$), a one-sided residue gap at precision $`m\le K`$ (room $`2H{+}J{+}K{+}2 < 2^m`$ and $`D(H,H+J,K)\bmod 2^m \le 2^m - (2H{+}J{+}K{+}2)`$) already forces $`{R}(2H{+}J) - {R}(H{+}J)\notin\mathbb Z`$. No lower margin at all is demanded. The proof chain is complete: the theorem holds for every $`a\ge 8`$, and *$`\text{cofinal upper-endpoint condition}`$ $`\Rightarrow`$ Irrational $`S`$* is proved.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L64)

```lean
theorem topEdgeResidueGap_unfolded (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_forces_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L75)

```lean
theorem topEdgeResidueGap_forces_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)
      ∉ Set.range ((↑) : ℤ → ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_orbit_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L83)

```lean
theorem topEdgeResidueGap_orbit_nonintegral {a K m : ℕ} (ha : 8 ≤ a)
    (hshort : K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a 0 K m) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_topEdgeResidueGapSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L92)

```lean
theorem irrational_of_topEdgeResidueGapSupply
    (hsupply : PowerTwoActualLcmTopEdgeResidueGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-proved-implications-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `topEdgeResidueGap_unfolded` | [E249_22/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L113) | [PaperStatementsAU.lean, line 486](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAU.lean#L486) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `topEdgeResidueGap_forces_nonintegral` | [E249_22/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L99) | [PaperStatementsAU.lean, line 470](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAU.lean#L470) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `topEdgeResidueGap_orbit_nonintegral` | [E249_22/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L106) | [PaperStatementsAU.lean, line 478](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAU.lean#L478) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `irrational_of_topEdgeResidueGapSupply` | [E249_22/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L94) | [PaperStatementsAU.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAU.lean#L187) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-chain"></a>

## Proposition 9.14 (Five sufficient conditions), page 86

> *Each of the five conditions below suffices for irrationality; none of them is proved. The first four imply the upper-endpoint condition; the fifth gives nonintegrality directly by the endpoint identity. These are not asserted to form a linear hierarchy. Here $`H=H(2^a)`$, and every condition quantifies over arbitrarily large exponents $`a`$.*
> 
> 1.  **Adjacent-suffix band*:
>     ``` math
>     \forall a_0\ \exists a,m,\ a_0\le a \wedge 8\le a \wedge m{+}1{+}(a{+}6)<2\cdot 2^a \wedge
>           2H{+}m{+}3 < 2^m \wedge
>     ```
>     ``` math
>     2H{+}m{+}2 \le \text{suffix residue}(2^a)\,0\,m \le 2^m - (2H{+}m{+}2)
>     ```
>     (a two-sided band on the adjacent-suffix residue directly, one candidate depth $`m`$).*
> 
> 2.  **Guarded odd-prefix band*: at the odd guarded depth $`2q{+}1`$, a two-sided band of half-width $`H{+}q{+}2`$ on the half-word residue modulo $`4^q`$. The depth is fixed by the stated guard; it cannot be chosen independently of $`a`$.*
> 
> 3.  **Guarded centred-magnitude bound*, *proved equivalent* to the previous one:
>     ``` math
>     \forall a_0\ \exists a,q,\ \max(14,a_0)\le a \wedge q=q_a
>           \wedge H{+}q{+}2 \le |u_{a,q}| .
>     ```*
> 
> 4.  **Flexible centred-magnitude bound*: the same magnitude bound with the depth restriction relaxed from “canonical guarded” to any odd $`2q{+}1`$ satisfying the half-cell fit $`2(H{+}q{+}2)\le 4^q`$ and the sign-corridor room $`2q{+}2{+}(a{+}6)<2\cdot 2^a`$.*
> 
> 5.  **Terminal dominance*: under the same bounds as item 4, $`\delta_{2^a}(2q+2)\le2u_{a,q}`$. This is a different one-sided comparison, treated immediately below.*
> 
> *For the first four conditions, the relevant implications into the upper-endpoint condition are as follows: adjacent-suffix band $`\to`$ upper-endpoint condition; guarded odd-prefix band $`\to`$ adjacent-suffix band; guarded centred-magnitude bound $`\Leftrightarrow`$ guarded odd-prefix band; flexible centred-magnitude bound $`\to`$ adjacent-suffix band; guarded centred-magnitude bound $`\to`$ flexible centred-magnitude bound.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_item_one_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L56)

```lean
theorem paperTeChain_item_one_unfolded :
    PaperAdjacentSuffixMidbandSupply ↔
      ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        m + 1 + (a + 6) < 2 * 2 ^ a ∧
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_two_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L113)

```lean
theorem teChain_item_two_unfolded :
    PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
          powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_three_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L124)

```lean
theorem teChain_item_three_unfolded :
    PowerTwoActualFinalTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q|
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L133)

```lean
theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q|
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_five_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L142)

```lean
theorem teChain_item_five_unfolded :
    PowerTwoFlexibleActualTerminalDominanceSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
          2 * actualOddHalfCenteredLift a q
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_five_sufficient_for_irrationality`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L214)

```lean
theorem paperTeChain_five_sufficient_for_irrationality :
    (PaperAdjacentSuffixMidbandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_first_four_imply_topEdgeSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L233)

```lean
theorem paperTeChain_first_four_imply_topEdgeSupply :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_fifth_gives_nonintegrality`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L271)

```lean
theorem paperTeChain_fifth_gives_nonintegrality :
    PowerTwoFlexibleActualTerminalDominanceSupply →
      PowerTwoActualLcmOrbitNonintegralitySupply
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_relations`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L254)

```lean
theorem paperTeChain_relations :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply)
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_or_of_paperAdjacentSuffixMidband`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L87)

```lean
theorem topEdgeResidueGap_or_of_paperAdjacentSuffixMidband
    {a m : ℕ}
    (hroom :
      ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlo :
      ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m)
    (hhi :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)) :
    ActualLcmTopEdgeResidueGap a 0 m m ∨
      ActualLcmTopEdgeResidueGap a 0 (m + 1) m
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L179)

```lean
theorem powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    PowerTwoActualLcmTopEdgeResidueGapSupply
```

where [`PowerTwoActualLcmTopEdgeResidueGapSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1325) is

```lean
def PowerTwoActualLcmTopEdgeResidueGapSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_paperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L190)

```lean
theorem irrational_of_paperAdjacentSuffixMidbandSupply
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

13. [`ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L197)

```lean
theorem paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
    (hsupply : PowerTwoOddGuardTopEdgeHalfWordBandSupply) :
    PaperAdjacentSuffixMidbandSupply
```

where [`PaperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L46) is

```lean
def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
```

14. [`ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L204)

```lean
theorem paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    PaperAdjacentSuffixMidbandSupply
```

where [`PaperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L46) is

```lean
def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
```

15. [`ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L69)

```lean
theorem paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
    (hsupply : PowerTwoAdjacentSuffixMidbandSupply) :
    PaperAdjacentSuffixMidbandSupply
```

where [`PaperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L46) is

```lean
def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
```

<a id="prop-te-chain-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperTeChain_item_one_unfolded` | [E249_22/Challenge.lean, line 289](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L289) | [PaperStatementsAX.lean, line 346](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L346) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `teChain_item_two_unfolded` | [E249_23/Challenge.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L238) | [PaperStatementsAX.lean, line 445](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L445) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `teChain_item_three_unfolded` | [E249_23/Challenge.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L231) | [PaperStatementsAX.lean, line 437](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L437) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `teChain_item_four_unfolded` | [E249_23/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L223) | [PaperStatementsAX.lean, line 428](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L428) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `teChain_item_five_unfolded` | [E249_23/Challenge.lean, line 214](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L214) | [PaperStatementsAX.lean, line 418](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L418) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `paperTeChain_five_sufficient_for_irrationality` | [E249_22/Challenge.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L276) | [PaperStatementsAX.lean, line 332](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L332) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperTeChain_first_four_imply_topEdgeSupply` | [E249_22/Challenge.lean, line 266](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L266) | [PaperStatementsAX.lean, line 321](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L321) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperTeChain_fifth_gives_nonintegrality` | [E249_22/Challenge.lean, line 261](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L261) | [PaperStatementsAX.lean, line 315](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L315) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperTeChain_relations` | [E249_23/Challenge.lean, line 197](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L197) | [PaperStatementsAX.lean, line 364](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L364) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `topEdgeResidueGap_or_of_paperAdjacentSuffixMidband` | [E249_23/Challenge.lean, line 257](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L257) | [PaperStatementsAX.lean, line 484](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L484) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband` | [E249_23/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L209) | [PaperStatementsAX.lean, line 377](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L377) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `irrational_of_paperAdjacentSuffixMidbandSupply` | [E249_22/Challenge.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L241) | [PaperStatementsAX.lean, line 226](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L226) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand` | [E249_22/Challenge.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L256) | [PaperStatementsAX.lean, line 309](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L309) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude` | [E249_22/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L251) | [PaperStatementsAX.lean, line 303](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L303) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband` | [E249_22/Challenge.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L246) | [PaperStatementsAX.lean, line 297](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L297) | [E249_22](../../evidence/comparator/replay-35882032091/receipt-E249_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-proved-implication"></a>

## Theorem 9.16 (The proved implication), page 87

> *The dominance hypothesis at a single odd rank already excludes integrality of $`\Omega_a`$, and the terminal dominance condition implies $`S\notin\mathbb Q`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.terminalDominance_orbit_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L217)

```lean
theorem terminalDominance_orbit_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hdom : diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_terminalDominanceSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L228)

```lean
theorem irrational_of_terminalDominanceSupply
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-proved-implication-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `terminalDominance_orbit_nonintegral` | [E249_23/Challenge.lean, line 248](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L248) | [PaperStatementsAX.lean, line 474](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L474) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `irrational_of_terminalDominanceSupply` | [E249_23/Challenge.lean, line 192](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L192) | [PaperStatementsAX.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L245) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-extension"></a>

## Proposition 9.18 (A sufficient extension), page 87

> *Either of the following suffices: (i) the lower-escape branch cofinally, as displayed just above; or (ii) the two-sided magnitude form (item 4 of Proposition 9.14), which asks only $`H{+}q{+}2 \le
> |u_{a,q}|`$ and which the Lean source proves implies corridor escape via a clean sign split (positive branch escapes above the terminal letter, negative branch escapes below the directed bound), without prescribing the sign of the centred representative. Neither branch is supplied by the conditional sign identity itself.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_lower_escape_supply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L236)

```lean
theorem irrational_of_lower_escape_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
      2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.corridor_escape_and_irrational_of_magnitude`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L252)

```lean
theorem corridor_escape_and_irrational_of_magnitude :
    (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L133)

```lean
theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q|
```

<a id="prop-sufficient-extension-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_lower_escape_supply` | [E249_23/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L182) | [PaperStatementsAX.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L221) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `corridor_escape_and_irrational_of_magnitude` | [E249_23/Challenge.lean, line 173](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L173) | [PaperStatementsAX.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L181) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `teChain_item_four_unfolded` | [E249_23/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L223) | [PaperStatementsAX.lean, line 428](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L428) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-separation-rational-approximation"></a>

## Theorem 9.19, page 88

> *Unconditionally, for every $`a`$ and $`q`$,
> ``` math
> \bigl|\, \Omega_a - \rho_{a,q} \,\bigr|
>   \;<\; \frac{4H + 2(2q{+}1) + 4}{2^{2q+2}} ,
> ```
> where $`\rho_{a,q}`$ is an explicit finite computable rational block. For fixed $`a`$, the error tends to zero as $`q`$ grows. In the quantified condition below, however, the depth is prescribed, so increasing $`q`$ is not a free way to satisfy the separation hypothesis.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L276)

```lean
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)))
        - actualLcmRawApprox a q|
      < (4 * (periodLcm (2 ^ a) : ℝ) + 2 * (2 * (q : ℝ) + 1) + 4) / 2 ^ (2 * q + 2)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.two_pow_odd_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L266)

```lean
theorem two_pow_odd_eq (q : ℕ) : (2 : ℝ) ^ (2 * q + 1) = 2 * (4 : ℝ) ^ q
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawApprox_isRat`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L312)

```lean
theorem actualLcmRawApprox_isRat (a q : ℕ) :
    ∃ v : ℚ, actualLcmRawApprox a q = (v : ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawErrorRadius_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L294)

```lean
theorem actualLcmRawErrorRadius_tendsto_zero (a : ℕ) :
    Filter.Tendsto (fun q : ℕ => actualLcmRawErrorRadius a q) Filter.atTop (nhds 0)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_actualLcmOrbitSeparationSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L320)

```lean
theorem irrational_of_actualLcmOrbitSeparationSupply
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-separation-rational-approximation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form` | [E249_23/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L163) | [PaperStatementsAX.lean, line 143](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L143) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `two_pow_odd_eq` | [E249_23/Challenge.lean, line 275](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L275) | [PaperStatementsAK.lean, line 102](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAK.lean#L102) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `actualLcmRawApprox_isRat` | [E249_23/Challenge.lean, line 169](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L169) | [PaperStatementsAX.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L158) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `actualLcmRawErrorRadius_tendsto_zero` | [E249_23/Challenge.lean, line 290](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L290) | [PaperStatementsAT.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAT.lean#L260) | [E249_23](../../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `irrational_of_actualLcmOrbitSeparationSupply` | [E249_24/Challenge.lean, line 88](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L88) | [PaperStatementsAX.lean, line 315](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAX.lean#L315) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-short-window-examples-through-exponent"></a>

## Theorem 9.22, page 88

> *``` math
> \forall a_0\le 6,\ \exists a,L,\ a_0\le a \wedge L < 2\cdot 2^a \wedge
>   \mathcal C(H_{2^a},H_{2^a},L)
> ```
> The single witness $`(a,L)=(6,93)`$ works for every threshold $`a_0\le6`$. Its certificate is verified by exact integer arithmetic on the finite totient windows. This proves the displayed bounded statement. It does not construct witnesses for unbounded thresholds; further finite checks would extend the verified range, not establish the universally quantified condition below.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_through_six_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L29)

```lean
theorem shortWindowSupply_through_six_paper (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_single_witness_six_ninetyThree`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L38)

```lean
theorem shortWindowSupply_single_witness_six_ninetyThree (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    a₀ ≤ 6 ∧ (93 : ℕ) < 2 * 2 ^ 6 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_witness_eq_t64_certificate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L47)

```lean
theorem shortWindowSupply_witness_eq_t64_certificate :
    certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ↔
      certifiedKill (periodLcm 64) (periodLcm 64) 93
```

<a id="thm-short-window-examples-through-exponent-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `shortWindowSupply_through_six_paper` | [E249_24/Challenge.lean, line 108](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L108) | [PaperStatementsAU.lean, line 425](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAU.lean#L425) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `shortWindowSupply_single_witness_six_ninetyThree` | [E249_24/Challenge.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L122) | [PaperStructuresN.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStructuresN.lean#L52) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `shortWindowSupply_witness_eq_t64_certificate` | [E249_24/Challenge.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L127) | [PaperStructuresN.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStructuresN.lean#L58) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-diagonal-certificate-table"></a>

## Theorem 9.24, page 89

> *``` math
> \forall t\in\{1,2,3,4,5,7,8,9,11,13,16,17\},\ \exists L,\
>   \mathcal{C}\ ({H}\ t)\ ({H}\ t)\ L
> ```
> at depths $`\{6,5,7,7,9,14,15,14,21,22,23,26\}`$ respectively, extended by separate computations to 28 historical values through $`t=64`$. The later aggregate theorem closes every scale $`t\le82`$ with no holes. Each witness is checked by exact integer arithmetic on two finite totient windows. For example, $`H_{17}=12252240`$ and $`L=26`$ use $`\varphi(H_{17}+i)`$ and $`\varphi(2H_{17}+i)`$ for $`1\le i\le26`$, not every totient between the endpoints $`12252241`$ and $`24504506`$. These computations verify the listed cases; they do not give a formula producing a certificate for every $`t`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerCertificateScales_list`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L22)

```lean
theorem diagonalPincerCertificateScales_list :
    diagonalPincerCertificateScales = [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17]
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerKillDepth_list`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L26)

```lean
theorem diagonalPincerKillDepth_list :
    diagonalPincerCertificateScales.map diagonalPincerKillDepth =
      [6, 5, 7, 7, 9, 14, 15, 14, 21, 22, 23, 26]
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_table`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L33)

```lean
theorem certifiedKill_diagonal_table :
    ∀ t ∈ diagonalPincerCertificateScales,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepth t)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_diagonalKill_on_table`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L40)

```lean
theorem exists_diagonalKill_on_table :
    ∀ t ∈ diagonalPincerCertificateScales,
      ∃ L, certifiedKill (periodLcm t) (periodLcm t) L
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_t64_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L46)

```lean
theorem certifiedKill_diagonal_t64_paper :
    certifiedKill (periodLcm 64) (periodLcm 64) 93
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_diagonalKill_le_82_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L52)

```lean
theorem exists_diagonalKill_le_82_paper (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_seventeen_window_data`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L59)

```lean
theorem periodLcm_seventeen_window_data :
    periodLcm 17 = 12252240 ∧ periodLcm 17 + 1 = 12252241 ∧
      2 * periodLcm 17 + 1 = 24504481 ∧ 2 * periodLcm 17 + 26 = 24504506 ∧
      diagonalPincerKillDepth 17 = 26
```

<a id="thm-diagonal-certificate-table-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `diagonalPincerCertificateScales_list` | [E249_24/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L136) | [PaperStatementsG.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsG.lean#L106) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `diagonalPincerKillDepth_list` | [E249_24/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L140) | [PaperStatementsG.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsG.lean#L109) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `certifiedKill_diagonal_table` | [E249_24/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L150) | [PaperStatementsI.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L152) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `exists_diagonalKill_on_table` | [E249_24/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L159) | [PaperStatementsI.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L163) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `certifiedKill_diagonal_t64_paper` | [E249_24/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L118) | [PaperStructuresN.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStructuresN.lean#L47) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `exists_diagonalKill_le_82_paper` | [E249_24/Challenge.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L155) | [PaperStatementsI.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L158) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `periodLcm_seventeen_window_data` | [E249_24/Challenge.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L171) | [PaperStatementsI.lean, line 177](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L177) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-extension-2"></a>

## Proposition 9.26 (A sufficient extension), page 89

> *``` math
> \exists C\ \forall t_0\ \exists t\ge t_0\ \exists L\le \log_2(4\cdot{H}\ t)+C,\quad
>   \mathcal{C}\ ({H}\ t)\ ({H}\ t)\ L .
> ```
> This asks for a certificate within a fixed additive constant of the necessary logarithmic depth bound. The uniform constant is an additional requirement, not a consequence of the finite data.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_logarithmicDepth_diagonal_supply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L58)

```lean
theorem irrational_of_logarithmicDepth_diagonal_supply
    (hsupply : ∃ C : ℕ, ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      L ≤ Nat.log2 (4 * periodLcm t) + C ∧
        certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_restrictedDepth_diagonal_supply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L72)

```lean
theorem irrational_of_restrictedDepth_diagonal_supply (depthBound : ℕ → ℕ → Prop)
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      depthBound t L ∧ certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-sufficient-extension-2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_logarithmicDepth_diagonal_supply` | [E249_24/Challenge.lean, line 164](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L164) | [PaperStatementsI.lean, line 169](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L169) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `irrational_of_restrictedDepth_diagonal_supply` | [E249_24/Challenge.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L98) | [PaperStatementsAU.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAU.lean#L184) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-one-common-certificate-sixteen-shifts"></a>

## Theorem 9.27, page 89

> *``` math
> \mathcal C(h,14,9)\qquad(h\in\{1,\ldots,16\}).
> ```
> The basepoint $`14`$ and depth $`9`$ are common to all sixteen shifts. Consequently, $`S\ne r`$ whenever $`r\in\mathbb Q`$ and $`\operatorname{den}(r)\mid2^{14}(2^h-1)`$ for some integer $`h`$ with $`1\le h\le16`$. The exact computation uses two nine-term windows for each shift and reduces their discrepancy modulo $`2^9`$. The earlier eight-shift computation uses basepoint $`12`$ and depth $`16`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_sixteen_shifts_basepoint_fourteen`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L85)

```lean
theorem commonCertificate_sixteen_shifts_basepoint_fourteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L91)

```lean
theorem totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne
    (r : ℚ) (h : ℕ) (h1 : 1 ≤ h) (h16 : h ≤ 16)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_eight_shifts_basepoint_twelve`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L98)

```lean
theorem commonCertificate_eight_shifts_basepoint_twelve :
    ∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16
```

<a id="thm-one-common-certificate-sixteen-shifts-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `commonCertificate_sixteen_shifts_basepoint_fourteen` | [E249_24/Challenge.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L208) | [PaperStatementsAT.lean, line 350](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L350) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne` | [E249_24/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L180) | [PaperStatementsAK.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAK.lean#L41) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `commonCertificate_eight_shifts_basepoint_twelve` | [E249_24/Challenge.lean, line 204](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L204) | [PaperStatementsAT.lean, line 347](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L347) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-simultaneous-certificates-unrestricted-depth"></a>

## Proposition 9.29 (Simultaneous certificates with unrestricted depth), page 90

> *The existence of a function $`f:\mathbb{N}\to\mathbb{N}`$ with $`f(N)\to\infty`$ such that
> ``` math
> \forall N_0\ \exists N\ge N_0\ \exists L\ 
>  \forall h\in\{1,\ldots,f(N)\},\quad \mathcal C(h,N,L)
> ```
> is equivalent to irrationality of $`S`$. Under irrationality, one can take $`f(N)=N+1`$, and every $`N`$ has a suitable depth.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_growingShift_simultaneous_certificate_iff_irrational`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SimultaneousShiftCertificateDepth.lean#L131)

```lean
theorem exists_growingShift_simultaneous_certificate_iff_irrational :
    (∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
        ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, ∀ h ∈ Finset.Icc 1 (f N),
          certifiedKill h N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_succ_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SimultaneousShiftCertificateDepth.lean#L122)

```lean
theorem exists_simultaneous_depth_succ_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N : ℕ) :
    ∃ L, ∀ h ∈ Finset.Icc 1 (N + 1), certifiedKill h N L
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SimultaneousShiftCertificateDepth.lean#L89)

```lean
theorem exists_simultaneous_depth_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N M : ℕ)
    (hM : 1 ≤ M) :
    ∃ L, ∀ h ∈ Finset.Icc 1 M, certifiedKill h N L
```

<a id="prop-simultaneous-certificates-unrestricted-depth-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_growingShift_simultaneous_certificate_iff_irrational` | [E249_24/Challenge.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L221) | [PaperStatementsAT.lean, line 461](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L461) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `exists_simultaneous_depth_succ_of_irrational` | [E249_24/Challenge.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L247) | [PaperStatementsAT.lean, line 505](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L505) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `exists_simultaneous_depth_of_irrational` | [E249_24/Challenge.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L241) | [PaperStatementsAT.lean, line 500](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L500) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-fixed-farey-bound"></a>

## Theorem 9.30, page 90

> *If $`S`$ is rational, its reduced denominator exceeds $`7.963\,964\,664\,670\,137\,532\,335\allowbreak\,577\,487\,583\,105\,3\times 10^{34}`$. This is the finite denominator exclusion in the corpus, logically independent of the certificate-supply reduction.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_rational_den_gt_fareyBound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L23)

```lean
theorem totientSeries_rational_den_gt_fareyBound (q : ℚ)
    (hq : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (q : ℝ)) :
    79639646646701375323355774875831053 < q.den
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.farey_gap_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L31)

```lean
theorem farey_gap_paper {a b c d r s : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1) (hleft : a * s < r * b) (hright : r * d < c * s) :
    b + d ≤ s
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_1_240_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L39)

```lean
theorem gapCheck_window_1_240_paper (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904)
        % 2 ^ 240 + q * 243 < 2 ^ 240
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_1_240_first_failure_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L48)

```lean
theorem gapCheck_window_1_240_first_failure_paper :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054
```

where [`IsFirstGapFailure`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GapFareyBound.lean#L44) is

```lean
def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)
```

<a id="thm-fixed-farey-bound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totientSeries_rational_den_gt_fareyBound` | [E249_24/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L186) | [PaperStatementsAK.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAK.lean#L46) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `farey_gap_paper` | [E249_24/Challenge.lean, line 266](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L266) | [PaperStatementsAJ.lean, line 322](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L322) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `gapCheck_window_1_240_paper` | [E249_24/Challenge.lean, line 277](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L277) | [PaperStatementsAJ.lean, line 348](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L348) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `gapCheck_window_1_240_first_failure_paper` | [E249_24/Challenge.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L271) | [PaperStatementsAJ.lean, line 343](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L343) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-extension-3"></a>

## Proposition 9.33 (A sufficient extension), page 91

> *Suppose $`g(K)\to\infty`$ and, for every $`K`$, the $`(N=1,K)`$ gap check excludes every rational of reduced denominator at most $`g(K)`$. Then $`S`$ is irrational: any rational value of $`S`$ would have a fixed finite denominator, contradicted at a sufficiently large $`K`$. Only unbounded exclusion bounds along a sequence of windows are needed for this argument. No equivalence with a bound for the continued-fraction denominators of $`S`$ is asserted; such a comparison would require its own proof connecting those convergents to the certified intervals.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_unbounded_window_one_gapCheck`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L68)

```lean
theorem irrational_of_unbounded_window_one_gapCheck (g : ℕ → ℕ)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop)
    (hcheck : ∀ K q : ℕ, 0 < q → q ≤ g K →
      (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (1 + r) * 2 ^ (K - r)) % 2 ^ K))
        % 2 ^ K + q * (1 + K + 2) < 2 ^ K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_one_excludes`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L58)

```lean
theorem gapCheck_window_one_excludes (K q : ℕ) (hq : 0 < q)
    (hcert : (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (1 + r) * 2 ^ (K - r)) % 2 ^ K))
        % 2 ^ K + q * (1 + K + 2) < 2 ^ K) :
    ∀ a : ℤ, (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ)
```

<a id="prop-sufficient-extension-3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_unbounded_window_one_gapCheck` | [E249_24/Challenge.lean, line 289](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L289) | [PaperStatementsAJ.lean, line 401](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L401) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `gapCheck_window_one_excludes` | [E249_24/Challenge.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L283) | [PaperStatementsAJ.lean, line 353](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L353) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-two-adic-congruence-that-does"></a>

## Theorem 9.34, page 91

> *The theorem is unconditional and holds for *every* $`K`$, $`H`$, $`B`$. For every $`K\ge 2`$, every $`H>K`$, and every bound $`B`$, there are primes $`p>B`$ with a length-$`(K{-}1)`$ zero prefix and a terminal half-modulus, giving
> ``` math
> D(H,p-K,K) \equiv 2^{K-1} \pmod{2^K}.
> ```
> Under eventual integrality this transfers to an integer $`z`$ with $`(z:\mathbb R) =
> {R}(p{+}H) - R_{p}`$ and $`z\equiv 2^{K-1}\pmod{2^K}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_half_pulse_window`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicHalfPulseAndAccumulatedResidue.lean#L26)

```lean
theorem exists_prime_twoAdic_half_pulse_window (H K B : ℕ) (hK : 2 ≤ K)
    (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K]
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.eventual_integral_tailDiff_twoAdic_half_pulse`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicHalfPulseAndAccumulatedResidue.lean#L41)

```lean
theorem eventual_integral_tailDiff_twoAdic_half_pulse {H K N₀ : ℕ} (hK : 2 ≤ K)
    (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K]
```

<a id="thm-two-adic-congruence-that-does-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_prime_twoAdic_half_pulse_window` | [E249_24/Challenge.lean, line 232](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L232) | [PaperStatementsAT.lean, line 481](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L481) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `eventual_integral_tailDiff_twoAdic_half_pulse` | [E249_24/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L212) | [PaperStatementsAT.lean, line 397](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L397) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-accumulated-residue-condition"></a>

## Proposition 9.36 (A sufficient accumulated-residue condition), page 92

> *Suppose that for every integer $`h\ge1`$ and every $`N_0\in\mathbb N`$ there are $`N\ge N_0`$ and $`L\ge1`$ such that
> ``` math
> D(h,N,L)\equiv2^{L-1}\pmod{2^L},\qquad
>  N+h+L+2<2^{L-1}.
> ```
> Then $`S\notin\mathbb Q`$: these two inequalities imply $`\mathcal C(h,N,L)`$, and the full quantified certificate condition applies. The half-modulus condition here is imposed on the accumulated weighted sum $`D(h,N,L)`$, not on a single totient difference. An unbounded set of triples with no control of the shift does not supply the displayed quantifiers. The required family remains unproved.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_accumulated_halfModulus_supply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicHalfPulseAndAccumulatedResidue.lean#L77)

```lean
theorem irrational_of_accumulated_halfModulus_supply
    (hsupply : ∀ h : ℕ, 1 ≤ h → ∀ N₀ : ℕ, ∃ N L : ℕ, N₀ ≤ N ∧ 1 ≤ L ∧
      windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L] ∧
      ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_halfModulus_residue`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicHalfPulseAndAccumulatedResidue.lean#L53)

```lean
theorem certifiedKill_of_halfModulus_residue {h N L : ℕ} (hL : 1 ≤ L)
    (hcong : windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L])
    (hsmall : ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    certifiedKill h N L
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

<a id="prop-sufficient-accumulated-residue-condition-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_accumulated_halfModulus_supply` | [E249_24/Challenge.lean, line 252](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L252) | [PaperStatementsAT.lean, line 588](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L588) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `certifiedKill_of_halfModulus_residue` | [E249_24/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L198) | [PaperStatementsAT.lean, line 342](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L342) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-arbitrarily-large-prime-power-lcm"></a>

## Theorem 9.37 (Arbitrarily large prime-power LCM jumps), page 92

> *For every $`t_0\in\mathbb N`$ there is $`t\ge t_0`$ with $`H(t)<H(t+1)`$. One may take $`t=p-1`$ for any prime $`p>t_0`$. The positions $`t=2^a-1`$ are also strict LCM jumps for $`a\ge1`$: $`2^a`$ is the next required power of $`2`$. The restriction excludes $`a=0`$, since $`H(0)=H(1)=1`$. The second condition in the next definition asks for the additional residue margin along this explicit sequence. Knowing these jump positions does not establish that margin.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_periodLcm_strict_jump_ge_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L26)

```lean
theorem exists_periodLcm_strict_jump_ge_paper (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ periodLcm t < periodLcm (t + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_prime_pred`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L31)

```lean
theorem periodLcm_strict_jump_at_prime_pred {t₀ p : ℕ} (hp : p.Prime)
    (hpt : t₀ < p) :
    t₀ ≤ p - 1 ∧ periodLcm (p - 1) < periodLcm (p - 1 + 1)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_powerTwo_pred`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L46)

```lean
theorem periodLcm_strict_jump_at_powerTwo_pred {a : ℕ} (ha : 1 ≤ a) :
    periodLcm (2 ^ a - 1) < periodLcm (2 ^ a - 1 + 1)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_zero_and_one_eq_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L59)

```lean
theorem periodLcm_zero_and_one_eq_one :
    periodLcm 0 = 1 ∧ periodLcm 1 = 1 ∧ ¬ periodLcm 0 < periodLcm (0 + 1)
```

<a id="thm-arbitrarily-large-prime-power-lcm-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_periodLcm_strict_jump_ge_paper` | [E249_24/Challenge.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L228) | [PaperStatementsAT.lean, line 467](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L467) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `periodLcm_strict_jump_at_prime_pred` | [E249_25/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L76) | [PaperStatementsAU.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L304) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `periodLcm_strict_jump_at_powerTwo_pred` | [E249_24/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L104) | [PaperStatementsAU.lean, line 318](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAU.lean#L318) | [E249_24](../../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `periodLcm_zero_and_one_eq_one` | [E249_25/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L81) | [PaperStatementsAU.lean, line 310](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L310) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-inequality"></a>

## Proposition 9.40 (A sufficient inequality), page 93

> *If, for every $`a_0\in\mathbb N`$, there is $`a\ge\max(2,a_0)`$ with $`\sigma_{2^a}\ge0`$, then $`S\notin\mathbb Q`$. This is the sufficient condition defined above, not a claim that the inequality holds at arbitrarily large indices. Equality at the edge is allowed: the condition is nonnegativity, not strict positivity.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_powerTwo_postJump_slack_supply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L90)

```lean
theorem irrational_of_powerTwo_postJump_slack_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a, max 2 a₀ ≤ a ∧
      0 ≤ canonicalAdjacentSuffixCentralSlack (2 ^ a)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalAdjacentSuffixCentralSlack_paper_formula`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L68)

```lean
theorem canonicalAdjacentSuffixCentralSlack_paper_formula (t : ℕ) :
    canonicalAdjacentSuffixCentralSlack t =
      min ((windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                (Nat.log2 (periodLcm t) + 10)
              - windowDiscrepancy (periodLcm t) (periodLcm t)
                (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10)
          - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5))
        (2 ^ (Nat.log2 (periodLcm t) + 10)
            - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5)
          - (windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                 (Nat.log2 (periodLcm t) + 10)
               - windowDiscrepancy (periodLcm t) (periodLcm t)
                 (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10))
```

<a id="prop-sufficient-inequality-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_powerTwo_postJump_slack_supply` | [E249_25/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L146) | [PaperStatementsAX.lean, line 339](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAX.lean#L339) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `canonicalAdjacentSuffixCentralSlack_paper_formula` | [E249_25/Challenge.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L129) | [PaperStatementsAX.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAX.lean#L264) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-certificate-four-tail-combination"></a>

## Theorem 9.41, page 93

> *Use $`J(H,p)`$, $`W(H,p,L)`$ and $`B(H,p,L)`$ from Theorem 6.60. For all $`H,p,L\in\mathbb N`$,
> ``` math
> B(H,p,L)<W(H,p,L)\bmod2^L<2^L-B(H,p,L)
>  \quad\Longrightarrow\quad J(H,p)\notin\mathbb Z.
> ```
> The bound $`B(H,p,L)=3pH+(p+1)(L+2)`$ follows by grouping the nonnegative remainders as in that theorem. Compared with the $`4pH+(p+1)(L+2)`$ bound obtained by treating the two diagonal differences separately, it saves $`pH`$. This is a strict improvement when $`pH>0`$; optimality for totient tails is not asserted.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpTailCommutator_notMem_int_of_central_window`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L36)

```lean
theorem primeJumpTailCommutator_notMem_int_of_central_window (H p L : ℕ)
    (hleft : (primeJumpSharpRadius H p L) < primeJumpWindowCommutator H p L % 2 ^ L)
    (hright : primeJumpWindowCommutator H p L % 2 ^ L
      < 2 ^ L - primeJumpSharpRadius H p L) :
    primeJumpTailCommutator H p ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_formula`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L31)

```lean
theorem primeJumpSharpRadius_formula (H p L : ℕ) :
    primeJumpSharpRadius H p L = 3 * p * H + (p + 1) * (L + 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_saves_pH`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L45)

```lean
theorem primeJumpSharpRadius_saves_pH (H p L : ℕ) :
    (4 * p * H + (p + 1) * (L + 2) : ℤ) - primeJumpSharpRadius H p L = p * H
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_lt_twoCellRadius`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L52)

```lean
theorem primeJumpSharpRadius_lt_twoCellRadius {H p L : ℕ} (hpH : 0 < p * H) :
    primeJumpSharpRadius H p L < (4 * p * H + (p + 1) * (L + 2) : ℤ)
```

<a id="thm-certificate-four-tail-combination-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `primeJumpTailCommutator_notMem_int_of_central_window` | [E249_25/Challenge.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L85) | [PaperStatementsAU.lean, line 325](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L325) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJumpSharpRadius_formula` | [E249_25/Challenge.lean, line 173](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L173) | [PaperStatementsAJ.lean, line 482](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L482) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJumpSharpRadius_saves_pH` | [E249_25/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L181) | [PaperStatementsAJ.lean, line 488](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L488) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJumpSharpRadius_lt_twoCellRadius` | [E249_25/Challenge.lean, line 177](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L177) | [PaperStatementsAJ.lean, line 485](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L485) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-one-explicit-witness"></a>

## Theorem 9.42 (One explicit witness), page 93

> *For $`H=H(4)=12`$, $`p=5`$ and $`L=15`$, direct integer evaluation gives
> ``` math
> W(12,5,15)=149906,\qquad
>  W(12,5,15)\bmod32768=18834,\qquad B(12,5,15)=282.
> ```
> Thus $`282<18834<32486`$, and $`J(12,5)\notin\mathbb Z`$. This is the one instance singled out in Theorem 6.60, not a claim of uniqueness or of the smallest possible height. The implication from a quantified family is Theorem 6.60.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_four_eq_twelve`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L62)

```lean
theorem periodLcm_four_eq_twelve : periodLcm 4 = 12
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJump_witness_twelve_five_values`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L68)

```lean
theorem primeJump_witness_twelve_five_values :
    primeJumpWindowCommutator 12 5 15 = 149906 ∧
      primeJumpWindowCommutator 12 5 15 % 32768 = 18834 ∧
      primeJumpSharpRadius 12 5 15 = 282 ∧
      (282 : ℤ) < 18834 ∧ (18834 : ℤ) < 32486
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpTailCommutator_twelve_five_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L76)

```lean
theorem primeJumpTailCommutator_twelve_five_notMem_int :
    primeJumpTailCommutator 12 5 ∉ Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_primeJumpSharp_supply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L81)

```lean
theorem irrational_of_primeJumpSharp_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ,
      0 < p ∧ primeJumpSharpKill (periodLcm t) p L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-one-explicit-witness-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `periodLcm_four_eq_twelve` | [E249_25/Challenge.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L73) | [PaperStatementsAU.lean, line 297](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L297) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJump_witness_twelve_five_values` | [E249_25/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L96) | [PaperStatementsAU.lean, line 334](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L334) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJumpTailCommutator_twelve_five_notMem_int` | [E249_25/Challenge.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L92) | [PaperStatementsAU.lean, line 331](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L331) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `irrational_of_primeJumpSharp_supply` | [E249_25/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L67) | [PaperStatementsAU.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L158) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-denominators-mobius-sums"></a>

## Theorem 9.44, page 93

> *For every integer $`t\ge5`$, with $`\mathcal P_t=\{p\text{ prime}:t/2<p\le t\}`$ as above,
> ``` math
> 2^{\lfloor t/2\rfloor}
>  \le\prod_{p\in\mathcal P_t}(2^p-1)
>  \le\operatorname{den}(H_t\beta_{H_t}).
> ```
> Moreover, some $`p\in\mathcal P_t`$ satisfies
> ``` math
> 2^{\lfloor t/2\rfloor}\le2^p-1<2^t,
>  \qquad 2^p-1\mid\operatorname{den}(H_t\beta_{H_t}).
> ```
> Indeed, Bertrand’s postulate makes $`\mathcal P_t`$ nonempty. Its members satisfy $`p-1\ge\lfloor t/2\rfloor`$ and $`p\le t`$, giving the size bounds. The divisibility follows from Proposition 6.6; divisibility of a positive reduced denominator also gives the product inequality.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.upperHalfMersenneProduct_between_bounds`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L110)

```lean
theorem upperHalfMersenneProduct_between_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ ∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p ∧
      (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ≤
        ((lcmHeight t : ℚ) *
          RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_upperHalf_channel_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L123)

```lean
theorem exists_upperHalf_channel_paper {t : ℕ} (ht : 5 ≤ t) :
    ∃ p ∈ upperHalfPrimes t,
      2 ^ (t / 2) ≤ RadicalMobiusShadow.mersenne p ∧
      RadicalMobiusShadow.mersenne p < 2 ^ t ∧
      RadicalMobiusShadow.mersenne p ∣
        ((lcmHeight t : ℚ) *
          RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_nonempty_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L98)

```lean
theorem upperHalfPrimes_nonempty_paper {t : ℕ} (ht : 2 ≤ t) :
    (upperHalfPrimes t).Nonempty
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_member_bounds`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L103)

```lean
theorem upperHalfPrimes_member_bounds {t p : ℕ} (hp : p ∈ upperHalfPrimes t) :
    t / 2 ≤ p - 1 ∧ p ≤ t
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_spec`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L94)

```lean
theorem upperHalfPrimes_spec (t : ℕ) :
    upperHalfPrimes t = (Finset.Ioc (t / 2) t).filter Nat.Prime
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmHeight_eq_periodLcm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L90)

```lean
theorem lcmHeight_eq_periodLcm (t : ℕ) : lcmHeight t = periodLcm t
```

<a id="thm-denominators-mobius-sums-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `upperHalfMersenneProduct_between_bounds` | [E249_25/Challenge.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L218) | [PaperStatementsAY.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L100) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `exists_upperHalf_channel_paper` | [E249_25/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L209) | [PaperStatementsAY.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L70) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `upperHalfPrimes_nonempty_paper` | [E249_25/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L229) | [PaperStatementsAY.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L109) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `upperHalfPrimes_member_bounds` | [E249_25/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L225) | [PaperStatementsAY.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L106) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `upperHalfPrimes_spec` | [E249_25/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L233) | [PaperStatementsAY.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L112) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `lcmHeight_eq_periodLcm` | [E249_25/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L152) | [PaperStatementsAX.lean, line 384](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAX.lean#L384) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `upperHalfMersenneProduct_between_bounds`:

```lean
theorem upperHalfMersenneProduct_between_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ ∏ p ∈ upperHalfPrimes t, mersenne p ∧
      (∏ p ∈ upperHalfPrimes t, mersenne p) ≤
        ((lcmHeight t : ℚ) *
          numericMobiusShadow (lcmHeight t)).den := by sorry
```

Challenge for `exists_upperHalf_channel_paper`:

```lean
theorem exists_upperHalf_channel_paper {t : ℕ} (ht : 5 ≤ t) :
    ∃ p ∈ upperHalfPrimes t,
      2 ^ (t / 2) ≤ mersenne p ∧
      mersenne p < 2 ^ t ∧
      mersenne p ∣
        ((lcmHeight t : ℚ) *
          numericMobiusShadow (lcmHeight t)).den := by sorry
```

<a id="prop-additional-approximation-hypothesis"></a>

## Proposition 9.46 (The additional approximation hypothesis), page 94

> *A sequence of rationals $`u_t`$ proves irrationality of $`S`$ if
> ``` math
> u_t\ne S\quad\text{for all sufficiently large }t,
>  \qquad \operatorname{den}(u_t)|S-u_t|\longrightarrow0.
> ```
> This is the rational-separation criterion of Proposition 6.22: if $`S=a/b`$ were reduced, every unequal $`u_t`$ would instead satisfy $`\operatorname{den}(u_t)|S-u_t|\ge1/b`$. An upper bound tending to zero for this product is needed. A lower bound for the denominator cannot establish it; improving a lower bound does not change the actual approximation error.*
> 
> *A different argument could deduce a residue certificate from the surviving divisor and further information about the complementary term. The denominator theorem alone contains no such separation statement. Neither sufficient argument is established by its lower bound, and these are not claimed to exhaust possible approaches.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_rational_separation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L137)

```lean
theorem irrational_totientSeries_of_rational_separation (u : ℕ → ℚ)
    (hne : ∀ᶠ t in Filter.atTop,
      ((u t : ℝ)) ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
    (h0 : Filter.Tendsto
      (fun t => ((u t).den : ℝ) *
        |(∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (u t : ℝ)|)
      Filter.atTop (nhds 0)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.den_mul_abs_sub_ge_one_div_den`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L149)

```lean
theorem den_mul_abs_sub_ge_one_div_den {q u : ℚ} (hqu : q ≠ u) :
    (1 : ℝ) / (q.den : ℝ) ≤ (u.den : ℝ) * |(q : ℝ) - (u : ℝ)|
```

<a id="prop-additional-approximation-hypothesis-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totientSeries_of_rational_separation` | [E249_25/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L163) | [PaperStatementsAJ.lean, line 423](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L423) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `den_mul_abs_sub_ge_one_div_den` | [E249_25/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L159) | [PaperStatementsAJ.lean, line 262](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L262) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-rationality-carry-rank"></a>

## Theorem 9.47, page 94

> *For every $`e\ge1`$, the retained dyadic totient sections form a basis for all sections through level $`e`$, of dimension $`2^e+1`$. The proof uses the Chinese remainder theorem and Dirichlet’s theorem. The complete level-zero truncation, consisting only of $`\varphi`$, has dimension one.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.retainedSections_basis_and_rank`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L79)

```lean
theorem retainedSections_basis_and_rank (e : ℕ) (he : 1 ≤ e) :
    (∃ b : Module.Basis (TotientCanonicalIndex e) ℚ
        (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))),
        ∀ i, (b i : ℕ → ℚ) = canonicalTotientKernelFamily e i) ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
        = 2 ^ e + 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.completeLevelZeroTruncation_is_totient_and_rank_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L93)

```lean
theorem completeLevelZeroTruncation_is_totient_and_rank_one :
    Set.range (totientKernelThroughLevelFamily 0) = {fun n => (Nat.totient n : ℚ)} ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_entries`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L33)

```lean
theorem canonicalTotientKernelFamily_entries (e : ℕ) :
    canonicalTotientKernelFamily e (Sum.inl 0) = (fun n => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily e (Sum.inl 1)
        = (fun n => (Nat.totient (2 * n) : ℚ)) ∧
      ∀ (j : Fin e) (r : Fin (2 ^ j.val)),
        canonicalTotientKernelFamily e (Sum.inr ⟨j, r⟩)
          = fun n => (Nat.totient (2 ^ (j.val + 1) * n + (2 * r.val + 1)) : ℚ)
```

<a id="thm-rationality-carry-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `retainedSections_basis_and_rank` | [E249_25/Challenge.lean, line 275](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L275) | [PaperStatementsBB.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L71) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `completeLevelZeroTruncation_is_totient_and_rank_one` | [E249_25/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L269) | [PaperStatementsBB.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L59) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `canonicalTotientKernelFamily_entries` | [E249_25/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L260) | [PaperStatementsBB.lean, line 24](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L24) | [E249_25](../../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-rationality-carry-rank-2"></a>

## Theorem 9.48, page 94

> *If $`S\in\mathbb{Q}`$, choose an integer $`v>0`$ with $`vS\in\mathbb{Z}`$ and put $`u_N=vR_N`$. Then $`u_N\in\mathbb{Z}`$, $`u_{N+1}=2u_N-v\varphi(N+1)`$, and $`0\le u_N\le v(N+2)`$. For every $`e\ge0`$,
> ``` math
> \dim_{\mathbb{Q}}\operatorname{span}
>  \{n\mapsto u_{2^j n+r}:1\le j\le e,\ 0\le r<2^j\}\ge2^e-1.
> ```
> The proof is given in Section 10.8.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.rationalValue_integral_carry_and_rank_floor`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L129)

```lean
theorem rationalValue_integral_carry_and_rank_floor
    {v : ℕ} (hv : 0 < v) {p : ℤ}
    (hvS : (v : ℝ) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (p : ℝ)) :
    ∃ u : ℕ → ℤ,
      (∀ N : ℕ, (u N : ℝ) = (v : ℝ) * totientTail N) ∧
      (∀ N : ℕ, u (N + 1) = 2 * u N - (v : ℤ) * (Nat.totient (N + 1) : ℤ)) ∧
      (∀ N : ℕ, 0 ≤ u N ∧ u N ≤ (v : ℤ) * ((N : ℤ) + 2)) ∧
      (∀ e : ℕ, 2 ^ e - 1 ≤
        Module.finrank ℚ
          (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))))
```

<a id="thm-rationality-carry-rank-2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rationalValue_integral_carry_and_rank_floor` | [E249_26/Challenge.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L49) | [PaperStatementsBJ.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsBJ.lean#L20) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-additional-hypothesis-totient-specific-rank"></a>

## Proposition 9.50 (An additional hypothesis for a totient-specific rank argument), page 95

> *A rank bound that contradicts the lower bound $`2^e-1`$ would have to use additional arithmetic of the actual totient coefficients. The generic proposal that every rational coefficient series has bounded tempered-carry rank is ruled out by the rational control recorded in the short paper: its carry rank is at least $`2^e-1`$ at every level. It is therefore not a remaining general lemma from which totient irrationality follows. The conditional Proposition 1.7 records eventual periodicity modulo $`v`$ together with unbounded rational rank. Periodicity of the residue sequences concerns values in a finite quotient; it does not bound the rational span of the integer-valued sections. The $`5/4`$ comparison shows that this distinction persists for a rational coefficient series.*

The Lean declarations below together state this result or one that implies it. For the rational $5/4$ comparison the Lean statement gives the eventual periodicity modulo $v$ explicitly, with period $2$ from index $2$ on every dyadic section, together with rank at least $2^e-1$ at every level $e$ and $0\le c(n)\le n$; the conditional totient statement (rationality of $S$ gives a tempered orbit with eventual periodicity modulo $v$ and rank at least $2^e-1$ at every level) is as printed.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.rationalControl_periodic_with_unbounded_carry_rank`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L238)

```lean
theorem rationalControl_periodic_with_unbounded_carry_rank :
    ∃ c : ℕ → ℕ, (∀ n, c n ≤ n) ∧ binaryCoeffSeries c = 5 / 4 ∧
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u ∧
          CarrySectionsEventuallyPeriodicMod v 2 2 u ∧
          ∀ e : ℕ, 2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.rationality_gives_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L256)

```lean
theorem rationality_gives_mod_period_and_unbounded_rank
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ, 2 ^ e - 1 ≤
          Module.finrank ℚ
            (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u
```

<a id="prop-additional-hypothesis-totient-specific-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rationalControl_periodic_with_unbounded_carry_rank` | [E249_26/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L81) | [PaperStatementsBH.lean, line 38](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsBH.lean#L38) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `rationality_gives_mod_period_and_unbounded_rank` | [E249_26/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L91) | [PaperStatementsBH.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsBH.lean#L57) | [E249_26](../../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
