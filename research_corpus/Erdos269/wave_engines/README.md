# Wave engines — Block-Kernel Programme computational layer

Curated, self-contained exact engines from the 2026-08-31 seven-wave campaign
(`BlockKernelProgrammeLab.md` is the governing document; every claim label and
erratum lives there, sections cited below). All decisions in these scripts are
exact integer/`Fraction` arithmetic or certified dyadic brackets; floats appear
only as scouting or display. Each file was independently re-verified by at
least one adversarial sibling agent during the campaign. These are evidence
engines and finite-certificate generators — nothing here proves the parent
theorem, and Erdős #269 remains OPEN.

| File | Role | Lab-note section |
|---|---|---|
| `engine.py` | Exact digit/radix engine (`e_a`, `b_a` via cumulative counters with exact repair of near-integer floors) plus width and window machinery; built for the J-certificate runs | §4–§6, §9 |
| `lattice.py` | Kernel-lattice machinery: `Λ = ker(c ↦ Σ c_r Ê′_r mod P/2)`, weighted-LLL basis search, obstruction-index `J` certification (`J = 1` iff an in-budget basis generates) | §6, §9 |
| `verify_headline.py` | End-to-end exact verifier of the headline exclusion certificate (`B_max ≈ 1.135×10^105`): re-derives `Ê′` from raw digits, checks `(i*)`, index `= P/2` by Bareiss, budgets, and the master inequality on certified enclosures | §9 |
| `headline_certificate.json` | The verified L = 128, m = 64 P-class certificate at `a₁ = 10005` (members, basis vectors, budgets, `B_max`) | §9 |
| `trace.py` | Standalone re-verified Euclid/Ostrowski trace for the (R1) parity renormalization (use this, never the retired wave-4 `renorm.py`) | §11 |
| `companion.py` | Multiplicative companion machinery: Lemma S shell splitting at `3^p ≈ 2^n`, Lemma T torus form, sliver accounting | §12 |
| `mrl.py` | The μ pseudo-norm layer: arc form of `F_p`, exact odd-measure `μ_p`, cocycle/block decomposition, rigidity law `μ_q = dist(q·log₅2, 2ℤ)` on range-1 blocks | §12 |
| `eng.py` | O(log p) floor-sum evaluator for `C_p(A)` on certified dyadic brackets (the wave-7 scale jump to `p ≤ 6.17×10^39`) with the (W)/(N)/(TEL) identity layer | §13 |
| `v0_selfcheck.py` | Self-check harness for `eng.py`: brute-force vs certified vs shell-count identities | §13 |

Known cross-file conventions: the campaign's `Y = 15X` normalization and the
corrected width `X_a ≤ a² + 6a + 11` (full height) are as pinned in the lab
note §1–§3; `Ê′ = Ê/30` throughout; μ-values predating the wave-6 complement
fix must be taken from the note, not from any older scratch output.
