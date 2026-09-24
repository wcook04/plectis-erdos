---
name: land-lean-proofs
description: Use whenever Lean proves or restates a result that a short paper or long record prints, or renames a declaration a paper links. Link the declaration in every paper that states the result, update its row in docs/paper_lean_coverage.json, queue the row for Comparator, and pass scripts/check_lean_paper_propagation.py. Palomar stays prepare-only.
---

# Land a Lean proof in the papers and the Comparator queue

A kernel-checked proof of a paper statement has landed when three things
hold: every paper that states the result links the declaration, the result's
row in `docs/paper_lean_coverage.json` records it, and the row waits in the
Comparator queue. `python3 scripts/check_lean_paper_propagation.py` fails until
they do, and `python3 scripts/check_release.py` runs it.

The convention that starts the reflex: a declaration that states a paper
result opens its docstring with the paper label in backticks, for example
``/-- **`res:foo`.** ... -/``. The check requires every such declaration in the
ledger, or in `docs/paper_lean_docstring_exemptions.json` with a reason.

## Steps

1. **Find every environment that states the result, short and long.** The
   short paper and the long record often label one result differently, so
   search by label, by declaration and by the statement's own words.

   ```sh
   python3 scripts/check_lean_paper_propagation.py --rows <label-or-declaration>
   grep -n '<phrase from the statement>' paper/<problem>/*.tex paper/reasoning-parts/erdos<problem>/*.tex
   ```

2. **Update each ledger row.** Set `lean.status` to `exact`,
   `exact_or_stronger`, or `modulo_named_input` with its `named_inputs`, and
   list every declaration by full name with its file under `lean/`, or under
   `verification/Erdos251LargeCertificate/` for the #251 large certificate,
   a separately built library the check also reads. For an
   exact row that Comparator has not compared, set `comparator` to
   `{"status": "pending", "queued_at": "<YYYY-MM-DD>"}` and `palomar` to
   `{"status": "pending"}`. Then run
   `python3 scripts/check_lean_paper_propagation.py --restamp` to rewrite the
   content digest. The maintainer regenerates the ledger from the coverage
   count; that run keeps `queued_at` and replaces a hand-written row with the
   counted one.

3. **Link the declaration where the statement is printed.** Nothing is written
   under the statement. Each result's evidence is two margin links, "Lean" and
   "Comparator", generated from the ledger into `paper/evidence/<paper>.tex`
   and placed beside the result from its `\label`; the paper's evidence record
   `evidence/<paper>.md` lists every declaration and check. Rebuild the paper
   with intermediates kept (`tectonic --keep-intermediates --outdir <dir> ...`)
   so the record can take the printed numbers from the `.aux`, then run
   `python3 scripts/paper_evidence.py build --corpus-repo <plectis-erdos-lean checkout> --aux-dir <dir>`.
   It refuses, and writes nothing, when a row cannot be resolved: no label, a
   declaration missing at the ledger's `lean_pin`, a Comparator association
   whose replay report does not show a passing check of the pinned corpus
   bytes, or a stronger Lean statement without a reviewed relation note in
   `evidence/relations.json`. Commit the records, set `record_commit` in
   `evidence/config.json` to that commit, run the build again so the margin
   links point at it, and rebuild the PDFs.
   The propagation check refuses a `\leannote` or a concordance block: that
   apparatus was retired. When the Lean proof assumes an input the printed
   statement does not, or covers only part of it, say so in plain words with
   `\evidenceremark{...}` directly after the environment's `\end{...}`.

4. **Correct the status prose.** Search both papers for "Conditional on",
   "conditional", "Not formalised" and "no Lean statement" near the result,
   in the coverage section and in any family catalogue, and restate what Lean
   now checks. Word it with
   [public-mathematical-writing](../public-mathematical-writing/SKILL.md).

5. **Rebuild and restamp.** Reassemble the long records, rebuild the changed
   PDFs and restamp their publication records through the chain in
   [propagate-research-consequences](../propagate-research-consequences/SKILL.md#paper-corrections-and-generated-consequences),
   then run `python3 scripts/check_problem_note_sources.py --coverage` for the
   printed links.

6. **Run the reflex check.**

   ```sh
   python3 scripts/check_lean_paper_propagation.py
   ```

   Each failure names its clause: (a) a ledger declaration its file does not
   declare, (b) a declaration no rendered link names, (c) a generated link
   naming a declaration the row does not bind, (d) a label-leading docstring
   outside the ledger, (e) a pending exact row without `queued_at`.

7. **Queue it.** Every exact row pending Comparator appears in the worklist
   the check prints. The maintainer's replay in the public corpus repository
   [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean) picks it
   up and records `compared` with its corpus entry, run id and corpus commit.
   Palomar is prepare-only: `prepared` means the compared corpus entry is
   ready, and nothing in this workflow submits.

## The baseline only shrinks

`docs/paper_lean_propagation_baseline.json` lists the (b) and (c) failures
present when the check was introduced, one row per entry, each with its
reason. A failure outside it fails the check. A listed failure that you repair
also fails the check until you delete its entry in the same change, and the
check refuses any entry it was not introduced with. Repair the link; never add
an entry.

## Exemptions

An entry in `docs/paper_lean_docstring_exemptions.json` names one declaration
that leads with a paper label and correctly stays out of the ledger: an
earlier conditional form, one clause of a larger statement, a verbatim copy.
Each entry gives the exact name, file, label and reason. Patterns are refused,
and an entry fails as stale once the ledger binds its declaration or its
docstring stops leading with that label.

## Boundary

Links and queue entries carry a kernel-checked result to its readers and
reviewers. They change no claim status, which `docs/claims.json` owns, and
Comparator checks only the restated statement, its axioms and kernel
acceptance.
