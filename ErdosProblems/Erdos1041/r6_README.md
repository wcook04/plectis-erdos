# Erdős #1041 — round-six return

## What changes the mathematics

The live 13/25 theorem has no root-location hypothesis. Its already registered scaling corollary therefore gives every squarefree monic polynomial a connection of length less than `2((25/13) mu)^(1/n)`, in the open level `(25/13) mu`. In every degree the length is less than `(5/2) mu^(1/n)` (use the exact quadratic segment in degree two). This is a consequence to expose, not a new theorem to attribute to this review. The 71/10 argument is retained as an independent area construction, not described as numerically strongest.

The new ordinary construction in `report/research_report.tex` covers

`F_(N,b)(z) = [z(z+b)]^N - (1+bz)^N`, for every `N >= 3` and `0 < b <= 1/(10N)`.

Invert the quadratic quotient `z(z+b)/(1+bz)` rather than the full polynomial. In the resulting coordinate the high-degree factor becomes `p^(2N)-1`; its phase cancels on two radial pieces, while the amplitude supplies a strict deficit on the intervening circular arc. Both the length and the level have explicit finite bounds. This removes the unspecified starting degree in the round-five asymptotic connector result, in the stated parameter range.

The exact degree-24 high-critical witness already certified in round five has a connection shorter than `58672129/117936000 < 1/2`, at level at most `3750/3763 < 1`. Its existing critical-value certificate was replayed: it has least critical modulus above `11/12` and fails every displayed radius-4/3 separation test. It is an explicitly easy metric example outside those scalar regimes, not a counterexample to the parent problem.

Retaining the perturbation's zero at the origin gives barriers at radius `delta^(1/(n-1))`. Together with the new connector, these prove a two-sided cusp law for the optimal all-curve distance in every fixed even degree `n >= 6`. This excludes a local Hölder estimate with exponent greater than `1/(n-1)` at `z^n-1` on the full closed-root-disc class. It does not establish a Hölder upper modulus for arbitrary perturbations, or a leading cusp constant.

All new geometric claims remain ordinary, advisory proofs: no independent review, Lean compilation or novelty claim is established. The parent remains open.

## Landable files

`edits/short_note_edits.json` contains 12 exact replacements against this packet's `01_short_note.tex`. `edits/apply_short_note_edits.py` refuses another base hash and writes a separate output. `edits/short_note.patch` is the corresponding unified diff. `edits/edit_plan.md` describes each anchor. `edits/long_record_transfers.md` preserves removed passages verbatim and gives destinations; the long record itself is not line-edited.

```sh
python edits/apply_short_note_edits.py PATH/01_short_note.tex --output PATH/01_short_note.r6.tex
```

The title, first theorem and entire first proof, and public commit pin are unchanged. The 13/25, 71/10 and radius-4/3 statements remain. No new sector or cusp theorem is inserted into the live note. The complete patched source and 20-page preview are extra aids, not an alternative source authority. The supplied input preview had 24 pages and already completed its opening proof on page one.

`report/research_report.tex` is the complete ordinary mathematical return; its compiled PDF has 11 pages. It includes the proofs, failure map and precise follow-up questions. `long_record_lag.md` records stale frontiers by label or unambiguous subsection. `lean/BlaschkeSectorConnector.lean` is a proposed module for `ErdosProblems/Erdos1041/`; see its separate README before importing it.

## Reproduce the executed checks

Use ordinary Python, not `python -O`. The new scalar checker, the existing high-critical checker and its complex-rational helper require only the standard library. The optional symbolic checker requires SymPy.

```sh
python checks/check_r6_constants.py
python checks/check_high_critical.py
python checks/check_symbolic_identities.py
```

The full live angular-budget checker was also replayed successfully, with 126 rational dual checks. Its unmodified source is included for convenience:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python checks/check_erdos1041_angular_budget_closure.py
```

Its floating linear programme is a proposer; rational upper bounds validate the result. The source includes a standard-library proposer fallback. The saved full-mode output is `checks/angular_budget_full_replay.json`. The final exponential inequality is independently checked with rational Taylor bounds in `check_r6_constants.py`.

The degree-24 enclosure JSON and checker were recovered unchanged from the round-five return because the round-six source slice omitted the JSON. `check_degree8.py` is retained as the exact-complex-arithmetic helper imported by `check_high_critical.py`; its separate degree-eight certificate was not replayed in this round and is not needed here.

These computations verify finite identities and numerical margins. The complex analysis, path construction and sector topology are proved in the report, not inferred from samples.

## Source authority and compilation

The input `01_short_note.tex`, `03_research_packet.json` and supplied source slice take precedence over both the older long record and public GitHub. Connected reads used the stated public pin `32545d77c4b5cfd72ebd36c8dcd2418bf7cc4d31` for exact declarations and a sibling conditional endpoint. No repository write was made.

The short-note preview was compiled using the supplied house style's pdflatex fallback and shared preamble. The repository release build can differ in pagination and sibling-document links. The report uses standard newpx fonts. No font files are distributed.

There was no runnable Lean workspace or Lean compiler in this session. The supplied proposed module has no `sorry` or new axioms, but is explicitly UNCOMPILED. Neither the existence of source code nor an exact Python replay is reported as a Lean or Comparator result.

To reproduce the optional previews with a normal TeX distribution:

```sh
(cd report && pdflatex -interaction=nonstopmode -halt-on-error research_report.tex && pdflatex -interaction=nonstopmode -halt-on-error research_report.tex)
(cd edits && TEXINPUTS=tex-runtime: pdflatex -interaction=nonstopmode -halt-on-error 01_short_note_diff_aid.tex && TEXINPUTS=tex-runtime: pdflatex -interaction=nonstopmode -halt-on-error 01_short_note_diff_aid.tex)
```

The second command uses the supplied shared-runtime sources, included in `edits/tex-runtime/` without any font files. Its compiled filename differs from the included `short_note_preview.pdf`, but the mathematical source is the same.
