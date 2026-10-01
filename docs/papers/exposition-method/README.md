<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Writing mathematics from the literature and reviewed revisions

A mathematical paper should let its reader identify the result, understand the
choices in its proof and recover the argument. The most useful models are
usually nearby papers: they show how the field names its objects, announces
hypotheses, connects deductions and gives space to a difficult step. General
writing advice helps interpret those choices; it does not replace reading them.

This guide extends the [public mathematical-writing skill](../../../skills/public-mathematical-writing/SKILL.md)
and [short-paper contract](../SHORT_PAPER_CONTRACT.md). They remain the working
instructions. The [rules](rules.json), [lesson records](lessons.json),
[historical proposals](history.json), [return identities](returns.json) and
[source records](sources.json) explain the evidence and exceptions behind this
guide. These are one evolving framework, with source history kept separate from
instructions a writer needs on each pass.

Start with [Writing a Good Mathematical Paper](../../../paper/exposition/writing-a-good-mathematical-paper.pdf):
two pages of general instructions usable by an author or AI assistant without
this repository. The [long companion](../../../paper/exposition/writing-mathematics-from-reviewed-revisions.pdf)
develops the worked cases and explains how successive reviews changed the
practice. Both [short](../../../paper/exposition/writing-a-good-mathematical-paper.tex)
and [long](../../../paper/exposition/writing-mathematics-from-reviewed-revisions.tex)
LaTeX sources, the companion's five inputs and their shared style are included
in the [version manifest](version.json) with the guidance.

## Keep the papers and agent instructions consistent

An edit to either writing paper includes a review of the
[mathematical-writing skill](../../../skills/public-mathematical-writing/SKILL.md).
Carry changed advice, examples and limits into its instructions in the same
change. If an edit leaves those instructions applicable, record the reason;
updating file hashes alone does not establish agreement.

After rebuilding the paper and its full-text copy, update the edition and file
hashes in [version.json](version.json). Its `paper_skill_review` binds the review
to the current paper inputs and skill, with an `updated` or
`verified_unchanged` disposition and a substantive reason. Run
`python3 scripts/sync_writing_skill.py --write`, then `--check`. This copies both
guides into the skill folder for independent installation. Projection and
release checks reject stale review bindings or bundled guides. Change the
paper sources and skill instructions, then regenerate their copies.

## Read the kind of paper you are writing

Choose a small set of human-authored papers close in subject and purpose. For
an irrationality argument, include a paper that actually passes from a rationality
assumption to a small nonzero integer. For a geometric estimate, include one
that explains the relevant component, map and measure. A survey, theorem note
and software paper need different models. A famous paper from a remote field
may be a useful comparison, but it does not establish the local terminology.

Read a complete local argument around each selected passage. Record the exact
edition, section and page or source label, and distinguish the author's text
from comments, metadata and later summaries. An abstract may settle a naming
question; it rarely supplies the proof's pacing. Do not mark a paper read because
its PDF was included in a packet. Record the portion actually inspected.

Look for decisions that can be explained, rather than words to imitate:

| Feature | Question to ask of a source passage | Use in a new draft |
|---|---|---|
| Terminology | What object does this term denote here? | Use the same established term only for the same object; otherwise state the definition. |
| Hypotheses | Where are domains, signs and quantifiers introduced? | Put the necessary assumptions in the claim and recall the one used at a difficult inference. |
| Sentence structure | Which clause supplies the reason for the next clause? | Let “since”, “hence”, “provided that” and “it remains to” express real mathematical relations. |
| Proof order | What has the reader learned before this construction appears? | State the needed estimate or target object before choosing its parameters. |
| Pace | Which step receives explanation, and which is abbreviated? | Spend space at the obstruction; do not expand routine algebra while skipping the hard step. |
| Attribution | Does the source prove, recall, adapt or merely compare? | Credit the actual result or construction at its use, with the correct version and locator. |
| Notation | What work does each new symbol do? | Introduce notation when it reduces repeated explanation; avoid another name for a familiar object. |

Write original prose in the field's conventions. Do not copy sentences,
imitate a named author's voice or impose one uniform cadence. Parallel
assertions often deserve parallel syntax; dependencies often deserve a
subordinate clause. Sentence variety is useful when it makes these relations
clear, not as a count to optimize.

## Let the proof determine the explanation

The model passage and the new argument must be compared in two separate ways.
First, identify the expository choice: perhaps the author names the integer
whose size will yield a contradiction. Then identify the local mathematics
that licenses the corresponding sentence. The source's writing choice does
not prove the new integer is positive, integral or small.

For example, Hančl and Tijdeman begin their Cantor-series argument by deriving
an integral scaled remainder from rationality (2004, proof of Theorem 2.1,
p. 373). The reviewed #269 exposition uses the same explanatory order:
rationality gives finitely many normalized tails, a sharper interval separates
the affine images, and deterministic recovery is needed before repeated tails
imply repeated blocks. The finite set of tails alone does not establish
periodicity. This is a reusable way to expose an inference, with a
problem-specific reason for the extra step.

A second example comes from Crmarić and Kovač (arXiv:2504.18712v1, Lemma 4(a),
pp. 4–5). Their construction maintains a finite remainder in a shrinking
interval, then uses convergence to identify the infinite sum. The #251
revision separates these same two explanatory jobs. Interval overlap permits
the next choice; the shrinking remainder proves attainment. A short example
of one choice establishes neither sparsity nor the limiting conclusion.

For terminology, compare the definition as well as the noun. “Stieltjes moment
sequence” names an established class in Wang and Zhu's paper; a private name
for its coordinates adds a second vocabulary. Conversely, established terms
such as “achievement set”, “upper Banach density” or “automaton state” should
survive a vocabulary pass when they denote the objects actually used. The
lesson is to remove needless decoding, not to eliminate technical language.

The R7 integrating reviews make the same test concrete. In #249, the local word
“tempered” was expanded to the actual condition `u(N)/2^N → 0`; “subexponential”
would have changed its meaning. In #243, removing “positive exact state” also
removed the referent of “the same assumptions”. The reviewer restored the
recurrences, natural-number domains and positivity where each was needed. These
are reviewed source selections; their later rendering and formal correspondence
remain separate checks in the return records.

Halmos's discussion of audience and organization (§§3–4) and Knuth, Larrabee
and Roberts's notes (§1, especially items 5 and 9–15) help explain these
choices. Gowers's examples-first discussion concerns where an example is
placed relative to an unfamiliar definition. Tao's warning against excessive
optimization explains why a useful paragraph may justify its length. None of
these sources supplies a universal page limit or a test of comprehension.
Exact versions and the portions inspected are recorded in [sources.json](sources.json).

## Review a proposed revision

Begin with the current theorem, its proof and its evidence. Settle disagreements
about mathematics before copyediting. For each substantive revision, retain:

1. The reader difficulty and the actual old passage.
2. The proposed new passage and its source location.
3. The literary model, its exact locator and the feature being adapted.
4. The mathematical checks that permit this wording, including any named input
   or pending formal comparison.
5. The integrating decision: accepted, accepted with a stated repair, rejected,
   already covered by the existing guidance, or pending a named check.
6. The range of application and a case in which the proposed advice would fail.

The agent with repository access applies the accepted change to the canonical
source, reconciles both paper forms and uses the native evidence and rendering
tools. A reviewer working from a frozen packet can propose revisions and report
checks, but cannot establish the state of a different live checkout. These
access roles are sometimes called Type A and Type B; they imply no ranking of
intelligence or independence.

A displayed formula can remain unchanged while its surrounding sentence changes
the claim. A common witness cannot be replaced by independently chosen witnesses;
a fixed-polynomial estimate cannot become a free-parameter family; an ordinary
argument cannot acquire full formal status from a nearby checked lemma. Keep
these as local mathematical obligations, not as generic stylistic exceptions.

## Revise the guidance without accumulating commandments

Most accepted revisions instantiate an existing rule. Add a new rule only when
the case supplies a reusable distinction not already expressed. State the
trigger, the action, the evidence and the limit. Keep the concrete example in
the ledger rather than enlarging the skill with every problem's vocabulary.

A source correction is itself instructive. The R6 #1049 return attached its
reader-motivation example to item 18 of Knuth's notes. Inspection of the original
places the passage in item 12, on the same printed page. The ledger retains the
reported locator and the correction. The editorial revision and its citation
are distinct objects of review.

Historical proposals also require judgment. A demand for the complete proof on
page one may diagnose a delayed elementary argument; it is unsuitable as a
universal requirement for a long theorem. An example may deserve to precede a
definition without preceding the paper's main result. A local failure of one
method should be retained with its witness, without becoming an impossibility
claim about every method. The [history](history.json) preserves such limits and
separates theorem-specific conditions from transferable advice.

## Use the revised version in the next packet

Include the current skill, this guide, the relevant rule and lesson records,
source identities and both writing papers. Freeze their bytes and digests in
the packet manifest. Enclose the actual primary sources needed for the chosen
passages, with version and reading-status information. The recipient should
read them and compare their conventions with the supplied manuscript, rather
than apply a generic vocabulary checklist. Source availability remains separate
from a declaration that a source was read.

The resulting change is a revision to repository documents and procedures.
It is not model training. An accepted passage, a successful build and a lower
stylistic-detector rate establish different things; none demonstrates improved
reader understanding. That requires observations from readers, with their task
and the compared versions recorded. Preserve unsuccessful revisions and source
limits so the next writer can make a better-informed decision.
