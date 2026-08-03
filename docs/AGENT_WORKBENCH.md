# The Agent Workbench

This corpus is agent-native. It is not an autonomous theorem prover and
is deliberately not trying to become one. It is a deep, instrumented
mathematical environment designed to be *inhabited* by an intelligent
agent — a reasoning model or a human — where the agent supplies the
search policy, the conjectures, and the judgment, and the environment
supplies what raw intelligence cannot supply for itself: exactness,
honesty, and replayability.

## Design thesis

Every mechanized proof-search policy we examined ends the same way: an
exact core it can fully justify (a kernel receipt, an algebra of
supports and cuts, a leakage-controlled evaluator) wrapped around a
policy layer it cannot (which candidate to probe next, which bridge
shape to invent, which representation to abandon). Systems ordinarily
fill that second slot with heuristics and then defend the heuristics.
We leave the slot open on purpose. The policy slot is occupied by an
agent with actual intelligence, and everything around it is built so
that the agent's work is exact where it must be and auditable
everywhere else.

Three consequences fall out of this inversion:

1. **Instruments, not pipelines.** Each tool here answers one question
   exactly and refuses to answer neighbouring questions it cannot
   ground. Nothing chains them automatically; the agent composes them.
2. **The unit of progress is the receipted session.** A session of
   reasoning — observations, conjectures with declared falsifiers,
   kernel probes, revisions, claims — is recorded as a durable artifact
   that a third party can replay end to end. The repository accumulates
   not just theorems but the audited cognition that produced them.
3. **Authority is structural, not rhetorical.** An agent cannot author
   a kernel verdict. Claims must cite kernel-accepted probe receipts,
   and the notary refuses the record otherwise.

## The instrument panel

| Instrument | Question it answers exactly | Entry |
|---|---|---|
| Proof-state compiler | Which candidate applications does Lean actually accept from this exact goal, and what are the exact resulting obligations? | `python3 scripts/proof_state_compiler.py --pilot-controls` |
| Blocker algebra | Three non-interchangeable projections: per-plan AND residuals (`plan_blocker_sets`), smallest additions completing some route (`minimal_missing_interventions`), smallest removals defeating every known route (`minimal_blocker_cuts`) | packet fields + `blocker_algebra_semantics` |
| Session notary | What did the agent observe, conjecture, probe, and establish — and can a stranger replay it byte-for-byte? | `python3 scripts/proof_workbench.py {open,note,probe,claim,close,replay,show}` |
| Blind harness | Can a candidate bridge be kernel-checked in a historical parent environment that provably lacks the future answer? | `python3 scripts/historical_bridge_experiment.py --compact` |
| Static semantic compiler | Which declarations are structurally relevant to this goal (nomination only — never applicability)? | `python3 scripts/query_corpus.py` |
| The corpus itself | More than 150,000 indexed declarations — 8,171 of them explicitly marked as generated certificate shards (a floor: further emitted families predate the markers), counted as source rather than as claims — across the reviewed library, problem-owned expansion, and auxiliary inventory forest; exact dependency neighborhoods cover both compact roots | `Erdos249257/`, `ErdosProblems/`, and `python3 scripts/query_semantic.py inventory` |

The last row is the quiet load-bearing one. This environment is deep
rather than broad: decades-hard problems, attacked far past the first
wall, with the failures formalized alongside the successes. Depth is
what makes probes decisive. When an agent conjectures here, the corpus
usually answers back — with a landed counterexample, a no-go theorem,
or an exact boundary — instead of with silence. A broad shallow corpus
cannot do that.

## The move grammar

A workbench session is a sequence of typed moves in an append-only
ledger (`workbench/sessions/<slug>/ledger.jsonl`):

- `observation` — what the agent read or measured, with sources.
- `conjecture` — a falsifiable guess. Conjectures should declare their
  falsifier; the notary records a warning when they do not.
- `plan` / `interpretation` / `abandonment` — the agent's reasoning,
  recorded honestly, including dead ends.
- `probe` — one Lean invocation. The notary stores the exact input
  bytes and computes the verdict (`kernel_accepted`,
  `kernel_accepted_with_sorry`, `kernel_rejected`) from the Lean exit
  status itself. Probes are the only moves that carry authority.
- `claim` — a statement bound to a cited kernel-accepted probe. The
  notary refuses claims citing anything weaker.
- `session_closed` — outcome plus move accounting.

`replay` re-runs every stored probe and reports whether recorded
verdicts still hold in the current environment. A session whose claims
survive replay is evidence; a session whose claims do not is a detected
drift, which is also evidence.

## The invention ladder

Agent-produced mathematics is claimed at exactly one of three rungs,
and the rung is part of the claim:

1. **Assisted proof.** The agent proved something with full access to
   the corpus. Claim: the theorem, its kernel receipt, and the session
   that produced it. No originality claim beyond what the ledger shows.
2. **Context-blind rederivation.** The agent worked inside the blind
   harness: a historical parent checkout that provably lacks the future
   module and name, with the future identifiers denied from its inputs.
   Claim ceiling: the agent rederived the bridge without access to the
   answer *in its context*. This does not rule out indirect exposure
   through model training; the claim is context-blindness, not
   training-blindness, and must be worded so.
3. **Prospective invention.** The agent proved a theorem that did not
   exist anywhere — in this corpus or its history — when the session
   opened. Blindness holds by construction: there was no answer to
   leak. This is the strongest rung, and the only one that supports the
   word "new".

Rung-3 sessions are the point of the whole design. The first landed
example is the carry-pivot session recorded in
`workbench/sessions/carry_pivot_2026_07_27/`, which produced
`Erdos249257/SuffixCylinderCarryPivot.lean`: the binary carry-pivot
normal form for numeral-adjacent boundary words and the exact
divisor-incidence identity that sharpens the previously landed
coarse `≤ +1` coefficient bound into an equality. The theorems were
derived and proved by reasoning agents inside this workbench, with the
kernel as the only judge, and the session ledger is committed beside
the mathematics.

## Evaluation

The workbench is judged on what it lets an inhabiting agent establish,
measured from ledgers rather than asserted:

- kernel-accepted probes per session, and probes-to-verdict per claim;
- refutation density — how often the corpus falsifies a conjecture
  (high is good; it means probes are decisive);
- ladder rung reached, with its receipts;
- replay integrity — whether closed sessions still verify from their
  stored bytes alone.

## Boundaries

- Ledger notes, rankings, and static nominations are advisory. Only
  kernel receipts assert.
- A bounded search that finds nothing is an abstention, never an
  impossibility claim. Family-level impossibility requires a landed
  theorem.
- Sessions record cognition; they do not certify that the cognition was
  optimal. The honesty is the feature.
- Nothing here claims progress on the open problem statuses tracked in
  `docs/RELATED_PROBLEMS.md` unless a landed theorem says so.
