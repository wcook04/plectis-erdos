# Formal evidence: The Binary Totient Series

This record belongs to the paper [erdos249-totient-reasoning-surface.pdf](../paper/249/erdos249-totient-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`c91562bd574a`](https://github.com/wcook04/plectis-erdos/tree/c91562bd574a387cde904481e609c7b4cacebb14) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 195 results: 191 with a Lean proof of the whole statement, 4 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 190 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

The record is divided by section of the paper.

| Part | Results | With a Lean proof | Compared |
|---|---|---|---|
| [Section 1](erdos249-totient-reasoning-surface/section-1.md) | 7 | 7 | 7 |
| [Section 2](erdos249-totient-reasoning-surface/section-2.md) | 9 | 9 | 8 |
| [Section 5](erdos249-totient-reasoning-surface/section-5.md) | 12 | 12 | 11 |
| [Section 6, results 6.1 to 6.38](erdos249-totient-reasoning-surface/section-6-1.md) | 32 | 32 | 31 |
| [Section 6, results 6.39 to 6.72](erdos249-totient-reasoning-surface/section-6-2.md) | 32 | 32 | 32 |
| [Section 6, results 6.73 to 6.103](erdos249-totient-reasoning-surface/section-6-3.md) | 32 | 32 | 31 |
| [Section 6, results 6.104 to 6.159](erdos249-totient-reasoning-surface/section-6-4.md) | 30 | 30 | 30 |
| [Section 9](erdos249-totient-reasoning-surface/section-9.md) | 27 | 27 | 27 |
| [Section 10](erdos249-totient-reasoning-surface/section-10.md) | 7 | 7 | 7 |
| [Section 12](erdos249-totient-reasoning-surface/section-12.md) | 7 | 7 | 6 |
