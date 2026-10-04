# Formal evidence: Distinct running least common multiples

This record belongs to the paper [erdos-269-three-prime-running-lcm.pdf](../paper/269/erdos-269-three-prime-running-lcm.pdf). For every result it lists the Lean declarations that state it, and the recorded Comparator check where there is one. The paper's verification concordance uses this result mapping.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`436f55ebdafa`](https://github.com/wcook04/plectis-erdos/tree/436f55ebdafa67e4af0fff79f621c13f2ded12bf) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 1 results: 1 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 0 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below. Comparator checks separately declared statements, the axiom budget and kernel acceptance; it does not establish novelty, significance or peer review.

<a id="res-distinct-height-235"></a>

## Theorem 1.1 (the sum over distinct running LCMs for $`\{2,3,5\}`$), page 1

> *The number $`\mathcal D_{\{2,3,5\}}`$ is irrational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos269.distinctHeightSum235_irrational`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos269/DistinctHeightIrrationality.lean#L689)

```lean
theorem distinctHeightSum235_irrational : Irrational distinctHeightSum235
```

<a id="res-distinct-height-235-comparator"></a>

**Comparator:** not yet compared.
