# Problem-corpus adapter

This directory is the owner root for the problem-centric Lean corpus. Read the
[`WORKING_GUIDE.md`](WORKING_GUIDE.md) before choosing a module, packet, or
computation; it is the maintained navigation surface for this tree.

## First contact inside a problem directory

1. If no problem number is already specified, first run
   `../../repo-python scripts/corpus_navigation.py --entry --json`. Its live
   `problem_choices` rows bind each supported ID to the owner directory,
   research packet, and supported Lean module without opening packets, running
   computations, or exposing claim-like state. Its `recommended_routes` map separates compact frontier selection, source
   topology, aggregate computation coverage, and selected-problem
   declared-script metadata, plus the selected problem's evidence neighborhood
   for papers, comparator corpora, and research handoffs. Then select the
   exact problem with the problem cockpit or
   `assimilation_manifest.json`; do not browse all problem folders looking for
   a starting point.
   For corpus-wide organization or source-shape work before a problem is
   selected, use the compact overview instead:

   ```sh
   ../../repo-python scripts/corpus_navigation.py --source-overview --json
   ```

   It reports compact location counts and manifest routing categories only;
   it does not open packets, run computations, or infer mathematical status.
   Each overview row also carries a non-executing `source_topology_command`
   to that problem's compact `--source-summary` view before directory-level
   inspection.
   The selected summary then carries `problem_cockpit_command` for its bounded
   evidence neighborhood and `source_inventory_command` for its exact path
   list only when that deeper inventory is needed. For a large owner directory,
   prefer `bounded_source_inventory_commands` to select Lean, Markdown, or
   scripts while keeping an explicit total and omitted count. From the Lean
   project root, for example:

   ```sh
   ../../repo-python scripts/corpus_navigation.py --problem erdos_<number> \
     --source-paths --source-kind markdown --source-path-limit 40 --json
   ```

   It is still filesystem navigation only; it does not run a script or infer
   mathematical status from a path.
   For an all-problem frontier chooser, use the bounded packet-metadata view:

   ```sh
   ../../repo-python scripts/corpus_navigation.py --frontier-overview --json
   ```

   It emits no target statements or identifier previews, runs no computation,
   and does not rank problems or infer mathematical progress.
   For corpus-wide mathematical interconnectedness, follow the entry card's
   `global_mathematical_connection_index`; choose one exact declaration from
   its bounded hubs before requesting directional concept/premise connections.
   Those graph edges are navigation evidence, not Lean proof dependencies.
2. Treat `Erdos<N>/research_packet.json` as the problem's research frontier
   and claim ceiling, and the exact Lean declaration plus focused build as
   formal authority.
   The selected `corpus_navigation.py --problem erdos_<number> --json` row's
   `problem_navigation_routes` keep packet, source, computation, and validation
   drill-downs together without executing any of them.
   For papers, comparator corpora, primary literature, or returned research,
   use the selected cockpit's bounded `evidence_neighborhood` before opening
   broad folders; it returns exact representative source routes without making
   those materials a second claim-status authority.
   For public-corpus or comparator identity, run `./repo-python -m
   system.lib.formal_math_corpus_registry --json` from the repository root.
   Its selected identity and paper views separate descriptor identity,
   optional checkout verification, navigation digests, and authored paper
   artifacts without opening the full descriptor at first contact. The source
   authority remains `codex/doctrine/formal_math_corpus_registry.json`. Use
   `--problem erdos_<number> --json` for the selected problem. All manifest
   problems share the same public applicability posture; current publication
   parity remains a separate fact, and routing is never theorem equivalence or
   proof transfer.
3. Keep new problem-specific Lean, notes, and computations inside that
   `Erdos<N>/` owner directory. Use the top-level `scripts/` directory only
   for corpus-wide support.

## Aggregate and change boundaries

- `Root.lean` is the supported problem-owned aggregate import;
  `AxiomAudit.lean` documents the aggregate's exposed assumptions. Keep their
  wiring explicit and avoid broad compatibility-import renames.
- A computation, audit, or prose note may guide investigation but cannot
  independently change a problem's public mathematical status.
- Before editing a shared packet, module, receipt, or import surface, claim
  its exact path and avoid files already owned by another active agent.
- For structural changes, run `../scripts/check_problem_corpus_index.py --json`
  from the Lean project root. For Lean changes, plan a focused wrapper build
  first; do not overlap focused and aggregate builds.
- The entry card and selected problem row also expose separate supported-root
  and `AxiomAudit` plans. Treat those as aggregate validation routes, not as
  proof or successful-build receipts.
