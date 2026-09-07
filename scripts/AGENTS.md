# Script-directory adapter

This flat directory contains corpus-level computational labs, audits, and
validation helpers. It is not a second problem index and it does not determine
mathematical claim status. Start with the parent
[`ErdosProblems/WORKING_GUIDE.md`](../ErdosProblems/WORKING_GUIDE.md) before
selecting a script.

## Choose the owner surface first

- For one problem, use the problem cockpit and then its
  `ErdosProblems/Erdos<N>/research_packet.json`; the packet names the open
  mechanism and claim boundary.
- For a cross-problem computation, query
  `./repo-python -m system.lib.formal_math_probe_registry --report` from the
  repository root. It maps named packet mechanisms to computation receipts.
- For supported Lean wiring, use `check_problem_corpus_index.py`. For Lean
  validation, use `lean_fast_build.py --plan <module>` before a focused build.
- To inventory script locations and filename-level operational roles without
  running any computation, start with `../../repo-python scripts/script_catalog.py`
  from the Lean project root. Use `../../repo-python scripts/script_catalog.py --json`
  only after selecting a drill-down: add `--problem 257` to restrict the
  result to files physically owned by that problem, or add `--role
  corpus_navigation` to find the read-only navigation helpers before searching
  the wider corpus. Add `--scope corpus` to exclude problem-owned scripts
  before browsing shared computational tools. It is a filesystem map, not a
  receipt registry.
- To join manifest ownership, supported Lean entry modules, and physical
  problem-owned script counts, use `../../repo-python scripts/corpus_navigation.py
  --problem 257 --json`. It is a navigation map, not a status dashboard.
- To map literal `problem_id` declarations in corpus-level scripts, use
  `../../repo-python scripts/corpus_computation_routes.py --json`. Each row
  supplies a `computation_surface_routes` join that keeps three meanings
  separate: physically problem-owned scripts, literal corpus-script metadata,
  and packet-bound probe receipts. Its `classification_boundary` explains why
  none of those routes alone is proof authority. Each row also supplies a
  non-executing problem-cockpit route for the selected problem's papers,
  comparators, and research handoffs.
- The same route reports bounded `unclassified_role_choices` for corpus scripts
  with no literal problem identity. Select one operational class before opening
  paths, for example `../../repo-python scripts/corpus_computation_routes.py
  --unclassified-role audit --path-limit 40 --json`. Here “unclassified” means
  only that literal identity metadata is absent; a filename or role never
  establishes relevance to a problem or recommends execution.
- Prefer a script inside `ErdosProblems/Erdos<N>/scripts/` when the work is
  owned by that exact problem. The files in this directory are corpus-level or
  historical support and should not be moved or renamed as a cleanup pass.

## Safe handling

- Open the selected script and its named packet/receipt before running it; do
  not batch-run filename families or infer status from a filename.
- A successful finite script run is an experiment receipt, not a proof or a
  solved-problem update. Keep status changes with the owning packet and Lean
  source maintenance lanes.
- Do not run a focused and aggregate Lean build concurrently. Use the wrapper,
  not raw concurrent `lake build`; wrapper exit `75` is ownership/capacity
  deferral, not a theorem failure.
- New organization checks belong here only when they are corpus-wide. Put
  problem-specific scripts under the corresponding `Erdos<N>/scripts/` owner
  directory instead.
