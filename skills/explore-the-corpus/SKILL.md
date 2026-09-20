---
name: explore-the-corpus
description: Read the public papers and proofs as one body of mathematics, decide what is worth developing, and grow that direction into a substantive contribution whose question, subject and form may emerge during the work.
---

# Explore the corpus

Use this skill when the request is open: read the mathematics and find what
comes next. The starting point is the corpus, and the question is an output of
the work. When the person already names a problem or an open statement, use
`skills/mine-open-problem/SKILL.md`.

The same research instruction is published for readers who work without a
clone. The region between the markers below is that instruction. The reading
edition embeds it unchanged, so the two presentations cannot drift apart.

## 1. Read in bulk before choosing

Load mathematics first and form a view second.

```sh
python3 scripts/query_corpus.py --overview --format card
python3 scripts/query_corpus.py --papers
```

The reading edition under `docs/reading-edition/` gives the short papers in one
file, with an index of the longer research records. Each paper is also
available as text under `docs/papers/full-text/`. Read several short papers in
full before comparing them. The longer records hold the computations, the
routes that stopped and the reasons they stopped.

## 2. The research instruction

<!-- BEGIN shared_research_instruction -->
**Read the mathematics as one body of work.** The papers cover eight Erdős
problems. Each problem also supplies methods, examples, obstructions and
stopped routes that may matter elsewhere. Decide what is worth developing. You
may stay inside one problem, connect several, bring in outside literature,
change the representation of an argument, or formulate a new question. The
worked examples in this edition are starting points. Other ways of working are
welcome.

**Choosing the question is part of the research.** A direction earns attention
when it explains something the papers leave unexplained, separates two
mechanisms, removes a hypothesis, exposes a false belief, or makes a recorded
result easier to understand and reuse. Say early what you think is worth
pursuing and why. Change course when the mathematics requires it, and keep the
abandoned route together with its reason.

**Develop a substantive contribution.** State its central idea, its relation to
the sources and why it matters. Say exactly what is proved, what is computed,
what is conjectured and what is missing. Attack your strongest claim before
presenting it. Search for prior work and cite what you find; a rediscovery
reported with its reference is a useful result. A careful partial argument, a
correction, a counterexample, a stopped route with a checkable reason, a
clearer explanation of an existing proof, and a well-posed new question all
count. Never announce a theorem in order to satisfy a format.

**Keep the sources exact.** The papers and Lean sources fix what may be claimed
about existing work. They place no limit on the questions you may ask. Quote
statements with their hypotheses. Keep finite evidence finite: a search that
has not excluded a case through depth N has shown exactly that, and membership,
existence and irrationality for all cases need their own arguments. Where a
tool or source is unavailable to you, name the limitation and leave the check
unclaimed.

**Return an account a mathematician can read.** Lead with the idea. Give the
argument in ordinary mathematical prose, then the evidence: code that reruns,
exact inputs and outputs, and Lean where you have it. Record the edition or
commit you started from, the people and tools involved, the limits of the
result and the next question it opens.
<!-- END shared_research_instruction -->

## 3. Words for finite searches

A finite search over candidates reports three outcomes and keeps them apart in
code, tables and prose.

- **Excluded by a finite certificate.** A finite computation shows the
  candidate cannot occur, and the certificate can be rechecked.
- **Finite representation found.** The search produced an explicit finite
  object with the required property.
- **Not excluded through depth N.** Neither of the above happened within the
  stated bound. This outcome carries no claim about larger depths.

## 4. When a direction emerges

Hand the direction to the existing workflows. They apply unchanged.

- A bounded statement to attack: `skills/mine-open-problem/SKILL.md`.
- Sustained work with appraisal of each stable result:
  `skills/run-coupled-research-goals/SKILL.md`. Record the emerging subject as
  the endpoint and revise it when the research changes it.
- Reader-facing mathematics: `skills/public-mathematical-writing/SKILL.md`.
- A stable result and its consumers:
  `skills/propagate-research-consequences/SKILL.md`. Update the papers the
  mathematics affects. Link the standalone account from the others.
- Lean checks: `skills/lean-concurrent-validation/SKILL.md`.

## 5. Where the work lives

A computation or investigation goes under `research/experiments/<name>/` with a
README that states the question, the exact procedure, the outputs and the
limits. Lean work goes in a module beside the declarations it uses. A new file
creates no claim status. `docs/claims.json` changes only through
`docs/METHODOLOGY.md`. A standalone account may concern several problems or
none of the eight. It keeps links to every source it draws on.

## 6. Return the work

Read `skills/erdos-research-return/SKILL.md`. A contribution that belongs to
one problem records that problem. A contribution whose subject is wider
records its subject in words and lists the related problems:

```sh
python3 scripts/continue_research.py start --help
```

Use `--subject` with zero or more `--related-problem` values. Never assign a
problem number the work does not have. Credit follows the returned objects and
decisions under `docs/research-commons/CREDIT_POLICY.md`.
