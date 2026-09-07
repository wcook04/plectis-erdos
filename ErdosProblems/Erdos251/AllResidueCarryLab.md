# All-residue telescoping countermodel

Type B file 05, Proposition D, independently checked as an ordinary
construction. The factorial word only hits residue `0`. The repair schedules
centres for every `(t, r, s)` with `s ∈ {2,4}` and realises those values as
gaps via a logarithmic even carry.

## What is kernel-shaped

r3 focused Lake receipt (2026-09-07):
`./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 2 ErdosProblems.Erdos251.AllResidueCarryCountermodel`
exit 0, 2472 jobs, serialized authority check passed; axioms `{propext, Quot.sound}` on
`alignResidue_modEq` / `allResidueCentre_modEq` / `allResidueGap_at_centre`, and
`{propext, Classical.choice, Quot.sound}` on `allResidue_partial_telescope`; no `sorryAx`.
Semantic identity digest `3d936c3706c4bf597980f584896df71164d272435486615971649b824c423168`.
This is a finite telescope over `ℤ`, not a `HasSum`.

- `alignResidue` / `alignResidue_modEq`
- pairing encoding of `(t, r, s)`
- strictly monotone centres, congruent to the scheduled residue
- finite telescope over `ℤ`:
  `Σ_{j < m} a_{N+1+j}/2^{j+1} = U_N - U_{N+m}/2^m`
- at a centre whose predecessor is not a centre, the gap equals the
  scheduled `2` or `4`

No `HasSum`, no positivity theorem, no prime-number-theorem cumulative
growth. Those remain ordinary (Type B's coefficient estimates; Python
probe `scripts/check_all_residue_countermodel.py --quick` checks the finite
telescope and centre gaps on a truncated range).

## What this is not

Not the actual prime-gap word. Not a proof that recurring `2` and `4` in
every residue class force irrationality; it is a countermodel to that
quantifier. Erdős #251 remains open.
