---
name: explain-public-system
description: Explain this public mathematical research system to a lay reader, mathematician, formaliser, compute contributor, reviewer, or infrastructure contributor from clone-local evidence.
---

# Explain the public system

Before following references or running repository commands below, locate the
intended Plectis public checkout and read its `AGENTS.md`. If this skill was
opened from an installed skills directory, open
`<checkout>/skills/explain-public-system/SKILL.md` in that checkout first.
Follow relative references from that clone-local file and run repository
commands from the checkout root. If the intended checkout is unavailable,
report that prerequisite before continuing.

Use this skill when a reader asks what the repository is, how it works, what it
has proved, or how they can take part. Base repository facts on tracked public
files; follow cited primary sources where the question requires them. Never
infer private state or turn an agent summary into proof authority.

When asked whether summaries show the **best results or actual nontrivial
progress**, first use the audit mode in
[`propagate-research-consequences`](../propagate-research-consequences/SKILL.md).
Do not simply repeat the overview's ranking or the current result guide. A
plain explanation of one already selected theorem does not need a corpus audit.

## Inspect a source or external record

For a bounded lookup, use the relevant row below before the whole-system
explanation. Follow only the selected record and its cited sources.

| Question | Route |
|---|---|
| Which declaration supports this result? | Query the claim with `python3 scripts/query_corpus.py --ask "<question>"`; follow its paper label or declaration handle into the source. [SOURCE_MAP](../../docs/SOURCE_MAP.md) explains those links. |
| Who proved this, and what should I cite? | Use `python3 scripts/query_corpus.py --route trace_prior_art`, then `python3 scripts/build_source_attributions.py --query "<name-or-problem-or-id>"`. Read the original statement and distinguish mathematical authorship, formalisation and local use. |
| Which paper edition or proof packet is recorded? | [Paper editions](../../docs/papers/README.md), [archive versions](../../docs/papers/archive_versions.json), and [Prove2Me packets](../../docs/research-commons/README.md#native-prove2me-theorems) identify the particular objects. Do not equate an archived edition with today's manuscript. |
| How does a formal statement match the upstream question? | Read the [Formal Conjectures crosswalk](../../docs/verification/FORMAL_CONJECTURES_CROSSWALK.md) and run `python3 scripts/query_corpus.py --route comparator_assurance` for the configured evidence. Compare the actual hypotheses and conclusions. |
| What can be prepared for Palomar? | Read [qualification](../../docs/verification/PALOMAR_QUALIFICATION.md) and run `python3 scripts/query_corpus.py --route palomar_qualification`. Follow its current candidate and remaining requirements. |

Record the exact source revision, declaration or edition, what it establishes
and what remains unchecked. When asked for current external status, verify the
original service or upstream record and distinguish it from the checkout's
dated receipt. Neither local readiness nor a stored success means a new
submission occurred. External submission requires explicit authorisation.

Return the requested source trail. A declaration lookup does not require a
Lean build; a correspondence review does not require a new Comparator run.
Use the reproduction branches below when the user requests those checks.

## Test one rational subsum candidate

For a request to test a rational candidate in the base-two reciprocal-Mersenne
achievement set, use the [exact probe guide](../../research/experiments/choices_contraction/README.md#the-probe)
and run the single-target command with that fraction. The documented
`189/388` example has outcome `not_excluded` through depth 16 and an exact
exclusion certificate at step 17. Record the input, host, depth, horizon,
selected prefix and any strict gap. `not_excluded` is only a finite observation;
it cannot certify an infinite representation. This computation does not
verify the weighted irrationality theorem or resolve universal Erdős #257.
For a terminal row, run the guide's `verify_terminal_witness.py` receiver
check on the JSON record before calling its exclusion or finite sum certified.

## Reproduce a selected Comparator theorem

For an explicit Comparator or #257 weighted-theorem reproduction request,
start with the [external verification replay guide](../../docs/verification/EXTERNAL_VERIFICATION_REPLAY.md).
Record an immutable public commit and tree, inspect the selected unit with:

```sh
python3 scripts/replay_external_verification.py plan --unit weighted-support \
  --source-commit <commit> --source-tree <tree>
```

Then use the guide's `run` command on Linux with systemd. Keep the resulting receipt with the exact
source revision. Report both the positive check and the deliberate mismatch,
the four contract failure controls, declared axiom budget, wall time and machine
details. A failed receipt or
missing platform prerequisite is a failure, not a theorem verdict. The
[replay guide's return section](../../docs/verification/EXTERNAL_VERIFICATION_REPLAY.md#return-a-replay-result)
routes the report through the existing research-progress form with its exact
source identity and evidence boundary. The
[reproducibility guide](../../docs/REPRODUCIBILITY.md) separately explains the
claim trail and Lean build; neither should be called an independent Comparator
run. The universal #257 assertion remains open.

## Reproduce one recorded claim

For an independent reproduction request, take this bounded branch before the
whole-repository explanation. Use Git and Python 3; Lean is not required.

1. Record the revision and local changes with
   `python3 scripts/agent_entry.py --checkout`. For latest-work requests, add
   `--check-upstream`; for a historical reproduction, use the requested tag.
2. Run `python3 scripts/verify_claims.py --list` if no claim was supplied.
   Otherwise use the given claim ID directly, for example
   `python3 scripts/verify_claims.py --claim eb_full_support`.
3. Inspect the returned declaration, assumptions, evidence and remaining open
   boundary. Report the exact command, exit status, Python version and commit.
   A failed check is a useful result: preserve its output and source location.
4. Return the report using `CONTRIBUTING.md`. A passing trail check is not a
   fresh Lean build or independent mathematical review. If the task needs
   proof elaboration, continue through `lean-concurrent-validation`.

Do not turn a first reproduction into installing the proof toolchain or reading
every paper. Stop when the requested claim trail and its limitations are clear.

## Build the explanation from the clone

1. Read `README.md` and `docs/READING_GUIDE.md` for the public promise.
2. Run the complete bounded overview:

   ```sh
   python3 scripts/query_corpus.py --overview --format card
   python3 scripts/query_corpus.py --papers
   ```

3. Read `docs/RESULTS.md` and the problem or paper handles relevant to the
   reader's question. Use `python3 scripts/query_corpus.py --ask "..."` for a
   narrower route. For a whole-system explanation, read the three companion
   papers below; for a bounded question, read only the papers and exact
   sections named by the corpus route.
4. Read `docs/METHODOLOGY.md` before explaining proof status, and
   `CONTRIBUTING.md` before explaining participation or credit.
5. Use the companion papers when the reader wants depth:
   - `claim-faithful-publication-systems-paper.pdf` for claims and publication;
   - `cold-clone-to-proof-receipt.pdf` for navigation and verification;
   - `open-source-mathematics-strategy.pdf` for the open-source strategy.

The agent performs this reading on the reader's behalf. Do not make prior
knowledge of the repository, Lean, Git, or the paper set a condition of entry.
Expose the exact source, paper section, declaration, or contributor route
behind each important statement so that the reader can inspect as much or as
little of the evidence as they want.

## Help a reader work through an argument

Find the named statement with `python3 scripts/query_corpus.py --ask "<question>"`
and open its paper and relevant source. Work at the depth the reader requested:
a complete explanation, an example, feedback on an attempt, or hints. If they
ask for hints, give one and wait for their attempt or request for more; do not
reveal the full argument in a later paragraph. Use their stated background,
and ask only when an unknown prerequisite would change the explanation.

Identify the difficulty that makes the decisive construction useful. Keep a
pedagogical reconstruction distinct from the recorded discovery history. When
checking a reader's attempt, point to the first unsupported step and preserve
what works. Do not turn a request to learn an existing argument into autonomous
research on an open problem. The [reading guide](../../docs/READING_GUIDE.md#work-through-an-argument)
offers a learner-facing entry. An explanation or successful navigation check
does not demonstrate that a reader has understood the result.

## Match the reader

For a lay reader, define Lean, a formal statement, a problem frontier, and a
pull request in ordinary English. Lead with one concrete journey through a
problem rather than a file inventory.

For a mathematician, lead with the exact endpoint, strongest unconditional
results, no-go results, cited literature, and remaining mathematical cut.

For a formaliser, bind informal claims to declarations, assumptions, source
coordinates, and the pinned toolchain.

For a compute or agent contributor, show the `mine-open-problem` route, its
stop condition, and the return path. Explain that useful output includes a
counterexample, exact computation, corrected statement, reproducible failed
route, or tooling improvement.

For somebody asking how sustained work operates, show
`run-coupled-research-goals`. Explain the discovery goal and stewardship goal
in ordinary language, how a stable delta wakes the second role, and why proof
status, mathematical appraisal, paper prominence, and the next allocation of
effort remain separate decisions.

For an infrastructure contributor, show the architecture proposal route and
the distinction between improving the conversion machinery and advancing a
mathematical claim.

## Required shape

For a whole-system explanation, answer four questions:

1. What is this repository trying to test?
2. What mathematical and technical objects are already here?
3. What can this reader do next, using one exact command or file?
4. What does that action not establish?

For that explanation, end with one copyable natural-language prompt, for
example: “Explain this repository to me as a mathematician and show me the
strongest result and exact remaining boundary,” or “Run one coupled research
cycle on a bounded frontier and return the evidence, consumer dispositions,
and next question.” The prompt is an entry convenience, not a new authority
surface.

Keep the authority order explicit: Lean checks the exact proposition in the
source; the claim registry controls the public description; papers explain;
external experts and mathematical communities decide broader acceptance over
time. Read the current problem count and status from
`python3 scripts/query_corpus.py --overview --format card`; do not freeze the
roster in this skill.
