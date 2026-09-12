# Papers and Lean source by problem

[Choose a problem on the website](https://wcook04.github.io/plectis/maths/).
Every problem has a short paper, a long paper, and a searchable source map.
PDF and TeX links point to stable file paths on this repository's `main` branch.
The website's HTML reader is a published snapshot.

`docs/problem_library.json` is the public machine-readable source for that view.
It is separate from the bounded `docs/problems.json` entry index. Each problem
contains `papers`, `paper_roles`, and a `source_map` with module nodes and import
edges. Import arrows describe source dependencies, not theorem strength or
mathematical credit. Only local Lean modules are included.

To refresh the library after changing source or paper records, run from a full
checkout (the reader-only sparse checkout intentionally omits Lean source):

```sh
python3 scripts/build_problem_index.py
python3 scripts/build_problem_index.py --check
python3 scripts/test_problem_library.py
```

Paper identities and short/long roles come from `docs/papers/corpus.json`.
Keep a paper's `paper_id` and file paths when revising it; rebuild and commit its
PDF with the TeX source. Title and page-count changes do not change its URL.
When adding a paper, its corpus record needs explicit problem membership
(`problem_ids`, or its existing numbered `subject`), publication state, form,
and paths to the PDF, TeX, and full text. Missing files fail the build.
The long manuscripts are assembled from `paper/reasoning-parts/`; use
`python3 scripts/assemble_reasoning_surfaces.py --check` to check agreement.

Source-map roots come from each problem directory, principal and companion
modules, reviewed result sources, and explicitly linked claims. The builder
reads actual Lean imports and follows their local dependencies recursively.
Each node carries its source digest and current GitHub URL; the library records
input digests so consumers can reject a mismatched claim snapshot.
