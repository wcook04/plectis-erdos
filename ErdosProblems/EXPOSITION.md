# Public exposition of this library

Each problem here now has a public paper of its own, an **Erdős Problem Note**
in `wcook04/plectis-lean-erdos249-257`. This file records which note covers
which packet, so a later agent does not re-derive the exposition, and so a
change to a packet's claim ceiling has a named public surface to check against.

Authored on branch `codex/problem-paper-series`, pinned to public commit
`4eb4c8ecfa0ad215248577263b583af0f5a36a62`.

| Problem | Packet | Public note | Surviving obligation named in the note |
|---|---|---|---|
| #243 | `Erdos243/research_packet.json` | `paper/erdos-243-reciprocal-tail-rigidity.tex` | `unbounded_negative_excursions` |
| #249 | `Erdos249/research_packet.json` | `paper/erdos-249-binary-totient-series.tex` | `totient_specific_moving_dyadic_escape` |
| #251 | `Erdos251/research_packet.json` | `paper/erdos-251-prime-gap-dyadic-series.tex` | `growing_block_dyadic_anti_concentration` |
| #257 | `Erdos257/research_packet.json` | `paper/erdos-257-mersenne-support-subseries.tex` | `connect_geometry_to_arithmetic_value_rigidity` |
| #269 | `Erdos269/research_packet.json` | `paper/erdos-269-three-prime-running-lcm.tex` | `uniform_prime_power_residue_escape` |
| #1049 | `Erdos1049/research_packet.json` | `paper/erdos-1049-rational-base-lambert.tex` | `three_halves_pade_height_gap` |

## Keeping the notes honest while the library moves

A note pins its links to one commit, so they can never break. The cost is that
a note can fall silently behind. That happened once, immediately and at scale:
the #243 module went from 146 to 1581 lines during the wave that followed the
first release of the notes, and closed the obligation the note named as open.
The note was still correct, because it is pinned and says what it is pinned to,
but it reached only 40% of the declarations that then existed.

The fix is a meter, not vigilance. `check_problem_note_sources.py --coverage`
reports, per problem, the fraction of currently existing declarations the note
links, and whether the modules changed since the pin, and it fails below
`note_coverage_floor` in `docs/problem_index_source.json`. Drift is now a
failing check with a worklist attached.

When a note drops through the floor: rewrite it against the current source,
repin `\commit` to a commit that is **pushed** — links resolve on GitHub, so a
local merge commit is not a valid pin — rebuild, and refresh the digests.

## Series contract

One note per problem. The notes share `paper/problem-note-preamble.tex`, which
fixes the house macros and the single pinned source revision every link
resolves against. `scripts/check_problem_note_sources.py` validates each
authored `(file, line, declaration)` triple against that snapshot **read out of
Git**, never the working tree, so later waves may move declarations freely
without decaying a published note.

A note expounds declarations of the `ErdosProblems` root. Those declarations
are exact Lean propositions and are **not** reviewed public claims:
`docs/claims.json` carries no row for them, and kernel checking the root does
not create one. The public registry states this as
`publication_architecture.problem_series_boundary`, and the contract checker
refuses a note whose authority posture drops it.

The existing `paper/erdos249-257-main-paper.tex` is intentionally not split or
length-limited. It is the integration monograph and may contain the complete
combined programme, cross-problem mechanisms, and every useful technical
detour. The #249 and #257 notes are independently readable projections and may
repeat as much of that material as their problem narratives require.

## Boundaries each note states in its own voice

- **#243** — the identification of the integer state system with reciprocal
  tails is exposition and is not formalised, and the two modules are not
  connected by a formalised derivation. The final bounded-negative-part theorem
  is stated as conditional, and its two analytic hypotheses, eventual strict
  centring and normalised vanishing, are listed as assumed and **not** derived
  from the growth hypothesis: it therefore constrains the state system, not the
  original sequence. The periodic exclusion assumes the regime `eₙ < aₙ`. The
  note also cites Erdős–Straus and Duverney, both stronger than anything
  formalised here.
- **#251** — every checked statement is finite or algebraic. The infinite form
  of the summation-by-parts identity needs the endpoint to vanish, and
  instantiating the abstract tail recurrence at the prime-gap tail needs
  summability; neither is proved, so nothing in the note concerns the infinite
  series. The constructive realisation of prescribed gap patterns by a free
  carry is marked unformalised.
- **#269** — the residue-escape consumer is presented as the trivial end of a
  strategy whose escape hypothesis is assumed. The height-fibre normal form is
  an identity between finite sums over a rectangular box, not over a smooth
  prefix.
- **#1049** — the Bundschuh–Väänänen criterion is external. Two of its inputs
  are formalised; three are named as not formalised. The corridor result is a
  no-go for one clearing scheme, not evidence about irrationality at 3/2.

## One correction the public check produced

The #269 packet's framing that the one- and two-prime cases are settled, and
that three is the first unresolved case, is **not** what Bloom's catalogue
records. What is recorded: the problem is open for every finite prime set of
size at least two; a single prime gives a rational sum; an infinite prime set
always gives an irrational one; and Erdős stated in a 1974 letter that he could
prove irrationality once duplicate summands are removed. The note states that
instead, and treats size three as its scope rather than as the frontier.

The same letter is worth carrying back here: removing duplicate summands is
exactly the reindexing by distinct running-LCM values, which is what the cell
and height-fibre theorems make precise.

## Deliberately not in the public notes

The finite Farey and truncation denominator exclusions for #269. Those
computations live in this repository at `scripts/check_erdos269_three_prime.py`
and are not part of the public release, so quoting their bounds publicly would
hand a reader a number with no artefact to check. The note names the obligation
to replace any finite exclusion by a family whose bound tends to infinity.

## Pending at public merge

1. **Register the notes in `tools/meta/dissemination/plectis_paper_registry.py`.**
   They are deliberately not rows in `PAPERS` yet. That registry describes what
   the public repositories ship on `main`, and both the corpus exporter and the
   site deploy resolve `tex_rel` and `pdf_rel` against `main`. Adding rows
   before the notes merge would point both at files that do not exist and would
   break the site deploy. When the branch merges, add six `Paper` rows with
   `home_repo="plectis-lean-erdos249-257"` and `hosted_pdf="papers/<stem>.pdf"`,
   then re-export the clone-local corpus so `docs/papers/corpus.json` carries
   them.
2. **Check the provenance contract against the rendered notes.** Each note
   reproduces the first-page provenance note and the invariant back-matter
   declaration verbatim from the shared preamble, so the existing anchors
   should hold; this has not been run, because
   `check_paper_provenance_contract.py` iterates the registry and the notes are
   not registered yet.
