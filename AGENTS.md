# Local Lean corpus adapter

This directory is a private, problem-centric Lean corpus. The repository-root
instructions still govern; this file only narrows first contact in this tree.

## Start here

1. Read [`ErdosProblems/WORKING_GUIDE.md`](ErdosProblems/WORKING_GUIDE.md).
2. If no exact problem number is specified, first list the supported IDs with

   ```sh
   ./repo-python formal_math/erdos257_period_noncollapse/scripts/corpus_navigation.py --entry --json
   ```

   This does not open packets or run computations. Its live `problem_choices`
   rows bind each ID to its owner directory, research packet, and supported
   Lean module while deliberately omitting claim-like state. Its
   `recommended_routes` map separates compact frontier selection, source topology, aggregate
   computation coverage, selected-problem declared-script metadata, and the
   selected problem's evidence neighborhood for papers, comparator corpora,
   and research handoffs.
   For a corpus-wide organization or source-shape task with no selected
   problem, use the compact overview instead of browsing every owner folder:

   ```sh
   ./repo-python formal_math/erdos257_period_noncollapse/scripts/corpus_navigation.py \
     --source-overview --json
   ```

   It reports only source-location counts and manifest routing categories;
   it does not open packets, run computations, or state mathematical status.
   Each overview row also carries a non-executing `source_topology_command`
   to that problem's compact `--source-summary` view, so use it before
   opening a large owner directory.
   Each selected source summary then carries `problem_cockpit_command` for
   the bounded papers, comparator, and research-handoff neighborhood, plus
   `source_inventory_command` for the exact path list only when needed. For a
   large owner directory, prefer its `bounded_source_inventory_commands`:
   they select Lean, Markdown, or scripts and preserve a total plus omitted
   count instead of opening every path at once. For example:

   ```sh
   ./repo-python formal_math/erdos257_period_noncollapse/scripts/corpus_navigation.py \
     --problem erdos_<number> --source-paths --source-kind markdown \
     --source-path-limit 40 --json
   ```

   This is still filesystem navigation only; it neither runs a script nor
   assigns mathematical meaning to a file name.
   For an all-problem frontier chooser, use the bounded packet-metadata view:

   ```sh
   ./repo-python formal_math/erdos257_period_noncollapse/scripts/corpus_navigation.py \
     --frontier-overview --json
   ```

   It emits no target statements or identifier previews, runs no computation,
   and does not rank problems or infer mathematical progress.
   For corpus-wide mathematical interconnectedness, follow the entry card's
   `global_mathematical_connection_index`; select one exact declaration from
   its bounded hubs before requesting directional concept/premise connections.
   Those graph edges are navigation evidence, not Lean proof dependencies.
3. Select one exact Erdős problem before opening a broad set of files. From the
   repository root, use:

   ```sh
   ./repo-python -m system.lib.mathematical_working_memory \
     --query "Erdos #<number>" --problem-cockpit --context-budget 12000
   ```

   The entry card exposes each selected problem's exact
   `focused_lean_build_plan`; use that before the separately labelled
   `release_aggregate_build_plan`. The selected `corpus_navigation.py
   --problem erdos_<number> --json` row exposes the same ordering alongside
   packet, source, and computation drill-downs without executing them.

4. Treat `ErdosProblems/Erdos<N>/research_packet.json` as the owner of the
   problem's frontier and claim ceiling. Treat the exact Lean declaration and
   focused build result as proof authority. Do not turn finite computation,
   a lab note, or a navigation projection into a solved-problem claim.
   For the public corpus or an external comparator checkout, start with `./repo-python -m
   system.lib.formal_math_corpus_registry --json`; select one corpus ID, then
   use its bounded `identity_view_command` or `paper_view_command` before
   opening the full descriptor or attached tree. The registry reader projects
   `codex/doctrine/formal_math_corpus_registry.json`; that JSON remains the
   registry authority. After selecting a problem, add `--problem erdos_<number>
   --json`. Every manifest problem receives the same public-corpus route; a
   zero-row result signals registry drift, not private or secondary status.
   A checkout candidate is not an identity match.

5. When the task is assimilating an arriving research return rather than
   continuing owned work, select the problem and then open its assimilation
   card before reading the return in depth:

   ```sh
   ../../repo-python scripts/assimilation_surface.py --problem <number>
   ```

   It relays return-batch custody, the packet's declared Lean boundaries, which
   claims are Lean-backed, the Comparator entries and their missing
   Palomar-required files, bound probe receipts, and the ordered downstream
   commands. It is routing only: it opens no Lean, runs no build, and never
   judges whether a return is correct, novel, or already known. Give the return
   byte custody through `tools/meta/bridge/type_b_return_intake.py` before deep
   reading; a return with no capsule row loses its source boundary at the first
   compaction.

## Layout and mutation boundaries

- New problem-specific work belongs under `ErdosProblems/Erdos<N>/`.
- `Erdos257PeriodNoncollapse` is shared historical machinery and a compatibility
  namespace. Do not perform broad import renames as organizational cleanup.
- `ErdosProblems/Root.lean` is the supported aggregate import and
  `ErdosProblems/AxiomAudit.lean` is executable assumption documentation.
  Keep aggregate wiring explicit.
- Before mutation, claim exact paths through the repository Work Ledger. Do
  not alter another active agent's Lean module, packet, receipt, or script.

## Navigation and validation

- Use the working guide's probe-registry commands to map computation receipts
  to named packet mechanisms and its consequence-map command after a source or
  receipt change.
- Plan imports before building:

  ```sh
  ../../repo-python scripts/lean_fast_build.py --plan <Lean.Module>
  ```

  Run that command from this directory. Use the wrapper, not raw concurrent
  `lake build`; focused and aggregate builds must not overlap. Exit `75` means
  the requested validation is already owned or capacity-deferred, not failed.
- Use the entry card or selected problem row for the live corpus structure
  check, focused problem plan, release aggregate plan, and aggregate
  axiom-audit plan. The aggregate route is an integration gate, not the routine
  first validation. A plan describes the validation partition; it is not a
  passing build or axiom receipt.
- Documentation-only changes require documentation checks, not a speculative
  Lean rebuild. For Lean source changes, validate the exact focused target
  before treating aggregate validation as a separate integration step.
