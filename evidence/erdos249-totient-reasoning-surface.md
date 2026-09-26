# Formal evidence: The Binary Totient Series

This record belongs to the paper [erdos249-totient-reasoning-surface.pdf](../paper/249/erdos249-totient-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`7f3dbf0947c3`](https://github.com/wcook04/plectis-erdos/tree/7f3dbf0947c387335ffd392b689eea5721017d84) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 195 results: 191 with a Lean proof of the whole statement, 4 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 191 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

The record is divided by section of the paper.

| Part | Results | With a Lean proof | Compared |
|---|---|---|---|
| [Section 1](erdos249-totient-reasoning-surface/section-1.md) | 7 | 7 | 7 |
| [Section 2](erdos249-totient-reasoning-surface/section-2.md) | 9 | 9 | 9 |
| [Section 5](erdos249-totient-reasoning-surface/section-5.md) | 12 | 12 | 11 |
| [Section 6, results 6.1 to 6.38](erdos249-totient-reasoning-surface/section-6-1.md) | 32 | 32 | 31 |
| [Section 6, results 6.39 to 6.71](erdos249-totient-reasoning-surface/section-6-2.md) | 32 | 32 | 32 |
| [Section 6, results 6.72 to 6.103](erdos249-totient-reasoning-surface/section-6-3.md) | 32 | 32 | 31 |
| [Section 6, results 6.104 to 6.159](erdos249-totient-reasoning-surface/section-6-4.md) | 30 | 30 | 30 |
| [Section 9](erdos249-totient-reasoning-surface/section-9.md) | 27 | 27 | 27 |
| [Section 10](erdos249-totient-reasoning-surface/section-10.md) | 7 | 7 | 7 |
| [Section 12](erdos249-totient-reasoning-surface/section-12.md) | 7 | 7 | 6 |
