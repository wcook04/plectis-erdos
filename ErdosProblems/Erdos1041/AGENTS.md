# Erdős 1041 local adapter

The parent problem-corpus adapter governs. This file only makes first contact
inside this owner directory exact and bounded.

1. From the repository root, open the problem cockpit before browsing files:

   ```sh
   ./repo-python -m system.lib.mathematical_working_memory \\
     --query "Erdos #1041" --problem-cockpit --context-budget 12000
   ```

2. Use the selected-problem control panel for `problem_navigation_routes` to
   the packet frontier, source inventories, computation surfaces, and
   validation plans:

   ```sh
   ./repo-python formal_math/erdos257_period_noncollapse/scripts/corpus_navigation.py \\
     --problem erdos_1041 --json
   ```

3. Ask the public-corpus registry for this problem before opening a checkout
   or descriptor:

   ```sh
   ./repo-python -m system.lib.formal_math_corpus_registry --problem erdos_1041 --json
   ```

   Every manifest problem has the same public applicability posture. A zero-row
   result signals registry drift, not private or secondary status; any returned
   link is routing metadata, not proof transfer.

4. **Before proposing any mechanism, read `research_packet.json` ->
   `negative_results`.** There are 22 of them and they are the elimination
   index for this problem; `exact_results` carries a further 28 rows, most of
   them mechanism eliminations with exact witnesses. This is not optional
   background. A 2026-08-23 session re-derived entries 9, 10, 15 and 17 from
   scratch -- the minimal-critical-value straight-spoke rule and the
   `n|v|^{1/n}` tree-length bound among them -- having opened this very file in
   its first command and read only the key names. Entry 17 even records *why*
   the bound looks canonical (`z^n - r^n` attains equality), which is exactly
   the observation that made it attractive the second time.

   Two habits follow. List the `.md` files in this directory rather than
   following only the cross-references of whichever lab you opened first;
   `StraightSpokeHubCriterionLab.md` section 4 alone holds four killed routes
   and is reachable from almost nothing. And check any new hub claim against
   the stored refutation witnesses before writing it down -- their margins run
   to `1e-5` in `1e-7`-thin corners of root space, so a float search will
   report a clean supremum pinned just under the threshold. Entry 19 is that
   lesson, already recorded.

5. `research_packet.json` owns the research frontier and claim ceiling. The
   exact Lean declaration plus a focused wrapper build owns formal validation.
   Plan the supported entry before building:

   ```sh
   ./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py \\
     --plan ErdosProblems.Erdos1041.CubicCriticalHub
   ```

   That focused plan checks the owner module. For a source-current replay of
   the complete supported owner route, use `--plan ErdosProblems.Root`; the
   root import list and the public packet's `landed_formal_source` are the
   authoritative module joins, not a promise that the open obligation is
   solved.

Finite scripts, papers, comparator corpora, returned research, and navigation
graphs are evidence or routing surfaces, not proof authority. Do not rename or
move Lean sources as organizational cleanup.
