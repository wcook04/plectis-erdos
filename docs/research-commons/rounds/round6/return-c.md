**I would now make one operation central to Plectis: use the checked difference between a returned claim and its target to determine what the next reasoner receives, how its return is assessed, and what the next experiment counts.**

That is where the restatements and failed routes can become productive assets. An equivalence can prevent double counting, supply an alternative presentation, expose a misleading completion claim, and define a controlled experiment. The same evidence should serve all four purposes.

My round-5 answer concentrated too much on producing additional interfaces. The round-6 evidence changes the priority: **make the existing interfaces and failure distinctions govern the actual Type A–Type B loop.**

**:chatgpt-content-reference{index="18"}[Download the complete round-6 return](sandbox:/mnt/data/plectis_round6_return.zip)**

The return contains the complete Python reference implementation for the first three builds, four Lean probe candidates, a source-bound audit, an evaluation protocol, and concrete edits for all three systems papers. **All 73 Python tests pass.** The executed audit imports all **70 supplied route rows**, examines **five actual corpus cases**, and constructs reproducible review packets. **The Lean candidates remain uncompiled; no fresh-reasoner experiment or live CI run is claimed.**

## 1. The verdict: improve the complete research loop

Type A’s diagnosis is substantially right, with an important qualification: **the history identifies productive uses of the corpus, but does not isolate their causal effect.**

The outcome ledger traces three lead results to targeted returns dated 5 September, followed by formalisation within the recorded 1–18-day interval. It also records valuable verification and attribution corrections. These are evidence that the wider programme has produced useful work. They are not a matched comparison proving that a particular packet design caused those results. :chatgpt-content-reference{index="0"} :chatgpt-content-reference{index="1"}

Meanwhile, the loop map identifies preventable losses: returned material without custody entries, working scripts and receipts outside version control, and packet manifests pointing into deleted worktrees. Those losses are independent of whether the mathematics was difficult or an attempted proof was good. :chatgpt-content-reference{index="2"}

The infrastructure should therefore be assessed across the entire passage:

\[
\text{accurate question}
\;\longrightarrow\;
\text{appropriate evidence}
\;\longrightarrow\;
\text{returned argument}
\;\longrightarrow\;
\text{valid assessment}
\;\longrightarrow\;
\text{durably usable result}.
\]

Optimising the number of declarations generated in the middle can leave the whole passage unimproved.

### What to preserve

Preserve the formal corpus, exact-statement comparison, axiom policy, paper-to-Lean correspondence, independent review and cold-clone verification route. Preserve the original returns, including rejected ones.

There is no justification for weakening acceptance checks merely because their cost is visible. The ledger’s corrections to false estimates and prior-art claims are part of the infrastructure’s value, even though they do not create another theorem. :chatgpt-content-reference{index="3"}

### What to consolidate

The active lane’s packet manifests, return intake, probe receipts, continuation record and propagation status should become **projections of one versioned record**.

The owner should be able to ask:

> What arrived for this exact packet? What did it actually establish? Which premises remain? What has been retained? Which required review, merge or paper update is still missing?

Answering those questions should not require reconstructing a session from temporary directories.

### What to freeze or remove from default execution

Freeze broad restatement-feature development until it has a named downstream consumer. Freeze regeneration of dormant metrics and expansion of general outreach or marketplace machinery that does not serve the observed loop.

Remove redundant hand-maintained status files as authoritative records once a checked projection replaces them. Archive dormant machinery rather than deleting its historical inputs.

There is also a correction to the “unused reductions” diagnosis: **no later formal import means no demonstrated formal downstream use.** It does not establish that a reduction never guided a reader, excluded an approach or supplied a useful presentation. Those other uses should be recorded prospectively instead of either assumed or dismissed retrospectively.

At the packet cutoff, the stranded results and unpropagated endpoint identified in the brief deserve attention before another producer is added. Their exact source versions and review limits must survive any rebase or worktree deletion. The supplied record distinguishes ordinary general proofs from the narrower formalised instances; that distinction must survive landing too. :chatgpt-content-reference{index="4"}

## 2. The source-level finding that explains part of the disappointing yield

The most important technical finding is in the pending round-6 engine, rather than in another proposed reasoning method.

In `engine_round6/part_core.lean`, lines 337–354 and 428–433, a changed hypothesis carries the contract

\[
\Gamma\vdash R\Rightarrow H,
\]

where \(H\) is the original hypothesis and \(R\) its replacement.

**This makes \(R\) sufficient for \(H\). In that same context, \(R\) is at least as strong as \(H\).**

At lines 416–419, the engine separately tries

\[
\Gamma\vdash H\Rightarrow R.
\]

When this succeeds, the two directions establish **equivalence**. The field named `weaker` records that converse success. It does not establish a strict weakening. Moreover, the code takes `.isSome`, discarding the reverse proof term.

This is not evidence of kernel unsoundness. The engine is proving the implication it says it proves. The problem is how that result is interpreted, named and counted.

### The immediate correction

Preserve both proof terms and report separate fields:

```text
forward_proved:       Γ ⊢ R → H
reverse_proved:       Γ ⊢ H → R
strictness_witness:   independently checked, or unknown
nonvacuity:           independently checked, refuted, or unknown
target_supplied:      independently established, or not supplied
```

A failed or timed-out converse search means **unknown**, not “strictly stronger”.

The numbers themselves need a smaller correction. The final per-problem columns reconcile once dropped hypotheses are included: round 5 has 14 given slots plus 21 converse successes; round 6 has 3 given slots plus 3 converse successes. The latter run reports 98 restated theorems and 100 restated slots. This is a classification issue, not an arithmetic discrepancy. :chatgpt-content-reference{index="5"} :chatgpt-content-reference{index="6"}

The local audit also records a stale run identifier in the round-6 subsection of `09_MACHINE_YIELD.md`: its header repeats the round-5 run, while the introduction names the round-6 run. The return keeps those identities distinct.

### This does not make every transformation useless

There are several different comparisons:

\[
H\Rightarrow U,\qquad U\Rightarrow E,\qquad R\Rightarrow U.
\]

A proof-body transformation can identify a consequence \(U\) actually used from \(H\), then reconstruct the consumer \(E\) from \(U\). That can genuinely weaken the original requirement.

A subsequent abductive replacement \(R\Rightarrow U\) concerns the intermediate predicate \(U\). It must not silently inherit a claim of weakestness or weakening relative to \(H\), still less relative to \(E\).

**Every comparison needs its operands and transformation history.**

### A second trap: comparing separately closed statements

The engine produces display forms by closing \(H\) and \(R\) over their separately needed binders. Its actual contract uses a common context. That common-context contract is the authority.

These statements are different:

\[
(\forall x,\ P(x))\Rightarrow(\forall x,\ Q(x))
\]

and

\[
\forall x,\ P(x)\Rightarrow Q(x).
\]

A graph rebuilt from display strings can lose the distinction. `ScopeCanary.lean` supplies a small regression candidate for it.

The prefix-scoped reconstruction itself is already present in the pending engine. I am **not** proposing the round-5 scoping fix again.

### Why a universal “progress score” would still be wrong

Even a perfect implication checker cannot rank all accepted theorems by research value. Once two propositions are both proved from the available background, each implies the other. A universal implication-based ranking would collapse distinctions between substantial results and trivial consequences.

For useful accounting, compare **residual predicates in a frozen pre-return context**, excluding the target and forbidden aliases where required. Separately record intended meaning, supply of the target, changed assumption or domain coverage, novelty assessment and observed usefulness.

The Aletheia evidence reinforces that separation. In its December 2025 campaign, the authors could classify 200 candidates as correct or incorrect; 63 were technically correct, but only 13 addressed the intended problem. The remaining 50 concerned an unintended reading. That is a finding about that assessed sample, not a general prevalence estimate for AI mathematics. Crucially, formal entailment alone cannot settle historical intent. :chatgpt-content-reference{index="7"}

## 3. The design: two linked records, with different rules for reuse

The main object should remain the **problem-sized research record**. Within it, store each research transition in two linked parts.

### The formal relation record

This contains exact predicates, their shared dependent context, permitted background, checked implications, scoped counterexamples and unresolved premises.

The implementation binds:

```python
@dataclass(frozen=True)
class Scope:
    environment: str
    telescope: str
    background: str
    anchor: str
```

The `anchor` identifies the independently reviewed version of the intended target. It is not merely a theorem name.

Rules have **all required premises**. A rule requiring \(A\) and \(B\) is not represented as two independently sufficient edges. The reference implementation computes a least fixed point, so an unseeded cycle cannot manufacture evidence.

Known mutual implications form an equivalence class for accounting. The original formulations remain accessible.

### The attempt and custody record

This contains what a reasoner actually received and attempted: packet identity, source availability, representation, failure cause, result, assessment, costs and later propagation.

Here the crucial distinction is between:

- a proved obstruction;
- a concrete counterexample;
- a finite check;
- an unsuccessful attempt;
- work outside the recorded evidence.

Those categories must remain distinct during reuse.

The local importer preserves all 70 supplied route rows and their reported classifications. It makes **zero new semantic certifications** merely by importing them.

### Two rules for extending the record

A checked proof of \(A\), together with a checked implication \(A\Rightarrow B\), can support a checked proof of \(B\).

A record that an agent succeeded on \(A\) at some cost, together with \(A\Leftrightarrow B\), **does not establish** that the agent would succeed on a fresh presentation of \(B\), or at the same cost.

That distinction matters when adapting replay ideas. Dream-RSI evaluates alternative policies by revealing outcomes already recorded along supported branches. Its retrospective evaluation does not award results for unrecorded branches. Plectis can extend its mathematical knowledge through proof, while still keeping its empirical observations restricted to attempts that actually occurred. :chatgpt-content-reference{index="8"}

### Failed attempts should produce repair questions

Consider the supplied B07 route. Its recorded difficulty involves unbounded tails and inability to recover coefficients from them. A different route whose source reports bounded tails and coefficient recovery is worth examining.

But the infrastructure should return:

```text
previous_attempt: B07
recorded_failure: unbounded tails; coefficient recovery unavailable
candidate_destination: distinct-height route
matching_properties: source-reported, requiring typed verification
prerequisite_set_proved_complete: false
route_viability: unknown
next_action: check the exact bridges and make a fresh attempt
```

It must not return “this route will work”.

Nor should it turn B07 into a universal ban on tail-based methods. The obstruction is tied to the attempted representation and its recorded conditions.

`transfer_questions` implements this conservative operation. Proved obstructions are deliberately handled separately, through their scoped theorem evidence.

## 4. Turn those distinctions into a packet compiler

The strongest synthesis is **a compiler for packets that preserve the distinctions most likely to be lost**.

Ordinary relevance retrieval asks: “Which passages concern this topic?”

This compiler asks:

> Which small, dependency-complete collection of evidence exposes the documented confusions that would make this particular return misleading?

For a target involving #1049, “the contour theorem” is not enough. The packet must also preserve its guards. For the #1041 path consumer, the packet must preserve the unsupplied split premise. For an equivalence to an irrationality target, it must preserve the difference between proving the equivalence and proving either side.

### The finite compilation problem

A request fixes the target, environment, source cutoff, mandatory context, budget and a **finite catalogue of distinctions to preserve**.

Each distinction has one or more owner-reviewed source or certificate bundles that expose it. The compiler chooses a dependency-closed set satisfying all those requirements within budget.

The reference implementation performs a bounded exhaustive search for the minimum visible byte cost over the supplied catalogue. If that search reaches its cap, it reports that optimality is unknown. If mandatory target information exceeds the budget, it refuses rather than dropping a guard.

This guarantee is intentionally precise:

> The selected packet covers every distinction in the supplied catalogue, using the dependency information supplied to the compiler.

It does **not** guarantee that the catalogue is complete, that the material will be understood, or that it is the minimum context needed for mathematical discovery.

### Why the existing failures can compound

One assessed error can become a shared evidence item with four uses.

First, it constrains the return gate: a restatement cannot be credited as target completion.

Second, it constrains the next packet: the distinguishing premise or guard must be visible.

Third, it becomes a regression case: subsequent changes must still detect that substitution.

Fourth, it defines an intervention: remove the failure explanation or change the representation, then test fresh reasoning under matched conditions.

The potential gain comes from **reusing the same assessment across these operations**, rather than paying four separate annotation costs.

This also avoids throwing away equivalent formulations. The graph compresses them for logical credit, while the packet compiler retains them as different presentations whose usefulness can be tested.

### What actually ran

The source-bound audit constructed a catalogue from five actual corpus cases. The completed search selected their five source spans plus mandatory task information:

| Executed construction | Result |
|---|---:|
| Curated distinctions covered | 5 |
| Search states visited | 11 |
| Selected packet, including task and manifest | 10,165 visible UTF-8 bytes |
| Corresponding five-full-file alternative | 124,191 visible UTF-8 bytes |

This is a reproducible selection result, **not a measured improvement in reasoning**.

A separate review example constructs packets with and without B07. Withdrawing B07 also removes the interpretation recorded as depending on it. The packets contain 5,935 and 3,770 visible bytes respectively.

Those are explicitly **review packets constructed after the historical replay**. They are not blinded rediscovery tests, and their size difference is not an effect estimate.

### Withholding must follow explanations as well as proofs

Deleting a theorem while retaining a paragraph explaining its decisive construction is not a holdout.

The compiler follows declared dependencies through source items and interpretations, as well as family exclusions and time cutoffs. The owner receipt contains withheld identifiers and reasons; those do not enter the reasoner’s ZIP.

An independent leakage review is still necessary. No dependency algorithm can remove an unrecorded dependence hidden in prose.

## 5. What this returns on the actual corpus

These are source-based classifications, with independent admission of the new relation records still pending. Full paths, line windows and hashes are included in `evidence/corpus_cases.json`.

Paths below are relative to `lean/ErdosProblems/`.

| Actual source | What the record should say | What it must not credit |
|---|---|---|
| `Erdos251/PrimeGapDyadicTail.lean:427–442` | `irrational_tsum_primeDyadicTerm_iff_primeGap` connects two irrationality views using the available summability result. Retain both views in one logical class. | Supply of either irrationality assertion from the equivalence alone. |
| `Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean:533–552` | Square-root escape and square escape are equivalent formulations. | Closure of the escape requirement. |
| `Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean:92–122` | Power and contour conditions are equivalent under `0 < b` and `b < a`. | A larger parameter region, or removal of those guards. |
| `ArgumentGraph/Results/Erdos1041.lean:8–75` | One maximality clause is vacuous off its switch; the added region is separately inhabited. | A verdict that the entire result is vacuous. |
| `Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean:258–276` | Several displayed assumptions are unused, but `SubcriticalSplitExists` remains a premise. | Proof of that split premise or parent completion. |

The last distinction is also explicit in the supplied frontier: the restated implication retains `SubcriticalSplitExists … → HasDistinctConnectionAtMost …`. :chatgpt-content-reference{index="9"}

These cases show why a single label such as “weaker”, “vacuous” or “progress” is inadequate.

For #251, the valid artifact is the equivalence and its useful presentations. A completion claim based only on that artifact fails the supply check.

For #1041, a clause can be vacuous while another clause is substantive. Conversely, unused assumptions can be removed while the essential open premise remains.

**Rejecting an unsupported completion claim should not discard the useful partial artifact.** That is the balance the return gate needs to enforce.

## 6. The first three builds, with code

The ZIP contains complete Python reference implementations for these operations. They are deliberately small and owner-operated. They do not replace the large-corpus exporter or the existing admission machinery.

### Build 1: capture every arrival and expose unfinished outputs

Files: `plectis_record/store.py`, `status.py`.

The store retains original bytes by SHA-256 and appends a hash-chained journal. The status projection links packets, arrivals, owner dispositions, retained outputs and required milestones.

A subtle requirement is implemented: **arrival identity is the capture-event identity, not the hash of the returned file**. Identical bytes returned against two different packets must not inherit each other’s assessment.

Different outputs can have different required milestones. An ordinary argument may require specialist review and publication. A formal result may require exact-target checking, kernel acceptance, merge and paper propagation.

A sealed round can contain rejected returns. Administrative closure is not mathematical acceptance.

The integration point is the actual handoff path: capture the packet before dispatch, capture every attachment before assessment, preserve complete probe output when it is obtained, and generate continuation views from this journal.

That addresses concrete losses in the supplied loop, including limited CI artifact retention and the runner’s retained output tail. :chatgpt-content-reference{index="10"}

A content hash is not authentication or backup. The implementation needs an independently retained journal head and durable storage.

### Build 2: exact relation queries and a conservative return gate

Files: `plectis_record/delta.py`, `probes/TypedRelationProbe.lean`.

The Python module checks exact scope and evidence bindings, preserves conjunctive premises, refuses unseeded circular support, and distinguishes equivalence, sufficient conditions, checked strictness and unknown comparisons.

It accepts attestations only from an independently controlled owner/CI set. A returned JSON object claiming “kernel checked” is not an attestation.

The Lean candidate shows the required proof-carrying shape: a common context, actual implication proofs, and actual separating witnesses where strictness is asserted. Its problem instances replay existing #251, #257 and #1049 relations.

**The production adapter binding those Lean records to the Python rule format is specified, but not implemented or executed in this return.** Begin with a small manually reviewed owner-issued map. Do not promote the five source annotations automatically.

This boundary matters because the supplied probe receipt explicitly distinguishes compilation from exact-target checking:

```text
evidence_class:       compilation_probe
exact_target_checked: false
environment_replayed: false
```

A successful compilation is therefore insufficient by itself to populate the semantic trust set. :chatgpt-content-reference{index="11"}

The first engine change should preserve the reverse implication proof, rename the misleading flag, and export the shared-context contract. Then expose the admitted record through the existing continuation query route.

### Build 3: reproducible packets and withdrawals

Files: `plectis_record/packet.py`, `query.py`, `audit_corpus.py`.

The compiler consumes immutable source objects rather than paths into disposable worktrees. It preserves mandatory context, checks dependency closure, enforces cutoffs and exclusions, selects the finite evidence basis, and emits a deterministic ZIP with a separate owner receipt.

The returned packet was independently rebuilt byte-for-byte through the CLI.

The local checks and reconstruction can be run from the extracted return directory:

```sh
python -m unittest discover -s tests -v

python -m plectis_record verify-store evidence/store

python -m plectis_record compile \
  evidence/store \
  evidence/contrastive-spec.json \
  /tmp/contrastive-review.zip
```

To import the supplied route record into an owner store:

```sh
python -m plectis_record import-routes \
  /path/to/05_REPLAY_ROUTES.json \
  /path/to/owner-store

python -m plectis_record status /path/to/owner-store
```

All **73 local tests pass**. They cover custody, implication direction, exact negative-evidence operands, scope mismatches, forged attestations, cycles, withdrawals, source exclusions, budget refusal and deterministic reconstruction. Unit-test attestations are fixtures, not corpus proof receipts.

The four Lean candidates should be submitted individually through Type A’s pinned probe lane. Their compilation, exact-statement audit and admission remain separate obligations.

## 7. Where this sits against the literature

The comparison needs to be demanding without inventing absence claims.

**An implication atlas is already established prior work.** The Equational Theories Project determined the implication or non-implication of all 22,028,942 ordered pairs among 4,694 laws, with Lean validation, and separately investigated finite settings. A Plectis claim based only on “we map equivalent and stronger statements” would not be distinctive. :chatgpt-content-reference{index="12"}

**Retaining verified partial proofs and reusable structures is also established.** ProofEvolve preserves partial AND-OR proof structures and transfers checked schemas while exposing residual premises. TWITCH learns abstractions from unsuccessful attempts and successful proofs of related conjectures. “We keep failures” is therefore not enough either. :chatgpt-content-reference{index="13"}

**Audited targets and linked explanatory records already have strong precedents.** Prove2Me separates immutable statements from proofs, audits a curated mission core and supports conditional proof sketches and readback. LeanArchitect connects formal developments with explanatory documents and dependencies. Plectis should reuse these ideas rather than present their absence as its motivation. :chatgpt-content-reference{index="14"}

The contribution to test is the **joint protocol**:

> A scoped relation and failure record generates the next finite packet, constrains the assessment of its return, and generates the exclusions and experimental units needed to measure whether that record helped.

That is more specific than a graph, a lemma library, a document system or retrospective replay alone. Its value depends on whether the operations remain consistent with one another and improve actual research transitions.

Global priority is not established by this review. The return’s `LITERATURE.md` gives the source-by-source comparison and the limits of each proposed distinction.

The desired compounding is also concrete. A useful representation might have little effect without the failure explanation that tells the reader why to use it. The failure explanation might have little effect without a representation in which the missing property is available. Their **interaction** is the research hypothesis, not an asserted speed-up.

## 8. The experiment that would establish that interaction

The supplied strategy paper already proposes ordinary repository access, a careful static brief, and a structured record as comparison conditions. Keep that strong static-brief control. Merely comparing the new system against an impoverished prompt would not test the claim.

### Start with faithful interpretation and usable assessment

Use independently reviewed task families involving guarded equivalence, an open premise, finite versus cofinal evidence, scoped refutation and clause-level vacuity.

A reasoner returns the intended target, what relation is actually established, the remaining premise, its evidence, and the exact next check required. Some comparisons should genuinely be unknown.

The first outcomes are unsupported completion claims, target substitutions, lost guards or quantifiers, recoverable citations, valid dispositions and maintainer repair time.

This pilot concerns the infrastructure’s handling of the corpus. It does not require claiming new solutions to the eight problems.

### Then separate representation from failure evidence

Within a frozen family, use a \(2\times2\) design:

| | Failure explanation withheld | Failure explanation included |
|---|---|---|
| Original presentation | Baseline presentation | Effect of failure evidence |
| Checked alternative presentation | Effect of representation | Joint effect |

Keep the intended target, mandatory safety information, model, tools and total expenditure policy fixed.

The interaction asks whether the failure explanation helps especially when the alternative representation is available. That directly tests the proposed combination of the two records.

Known equivalents and explanatory descendants belong to one experimental family. The recorded 103-member disguise class must not become 103 independent successes. The packet’s census of 642 classes and 627 target-restatement bundles is useful for identifying this issue, not for inflating the denominator. :chatgpt-content-reference{index="15"}

### Charge the whole cost

Include packet authoring, catalogue curation, retrieval, model inference, failed probes, assessment, repair, landing and maintenance. Distinguish cached from uncached expenditure.

This is necessary in light of Berlot-Attwell and colleagues’ findings: in the three library-learning systems they studied, apparent gains did not consistently survive matched computational accounting; their closer examination of LEGO-Prover also found no evidence of direct learned-lemma reuse in that setting. These are warnings about evaluation, not a theorem that reusable records cannot help. :chatgpt-content-reference{index="16"}

Do not infer benefit from a stored proof disappearing when an interface is withdrawn. Fresh search may reconstruct it cheaply. Conversely, equivalent representations can reduce search cost while adding no logical consequence.

The delivered evaluation protocol distinguishes stored-derivation withdrawal, fresh interface-use trials and historical holdouts. **Only the first and packet construction are implemented here. No comparative reader result is claimed.**

## 9. Rebuild the three papers around the observed workflow

The papers need different jobs.

### Main systems paper: the actual research transition

Lead with one concrete distinction between a target and a returned argument. Then describe the operator-relayed Type A–Type B workflow, the formal and observational records, packet compilation, assessment and propagation.

Report the outcome ledger, the naturalistic route replay, the measured restatement yield and the implementation audit separately. Give the matched-reader experiment its own section, clearly marked as proposed.

Do not say the existing papers contain no roles or evaluation discussion. They do. What needs a precise account is the **actual deployed relay**, with its packet versions, custody, timing and losses.

A replacement abstract supplied in the return begins:

> Plectis maintains a formal research corpus together with the arguments, failed routes, source comparisons and unresolved premises needed to use it. The deployed workflow combines an owner working in the repository with external reasoners working from fixed packets supplied through an operator. Returned arguments are checked, assessed and propagated into the corpus and its papers. We describe the evidence and authority at each transition.
>
> The record spans eight problem programmes and includes formal implications, scoped counterexamples and multiple formulations of unresolved statements. A reference extension uses this material to compare predicates in an exact context and to compile reading packets that preserve a finite catalogue of important distinctions. It records equivalent views without counting them as independent advances, and retains failed attempts without treating them as universal obstructions.

The rest of that abstract states the evidence and the unrun evaluation explicitly.

### Strategy paper: allocation, reuse and stopping rules

Make this the account of when to commission another round, reopen a recorded route, seek a missing source, request specialist review, or finish propagating existing work.

Retain its serious static-brief comparison. Add the representation-by-failure experiment and the full cost model.

A useful replacement principle is:

> A failed attempt records a result under specified conditions. Reopening it requires an explicit change to those conditions or new evidence about the blocked step. A recorded obstruction can exclude a matching proposal; an unsuccessful attempt alone cannot.

The stopping rule should also be explicit: if catalogue curation costs more than it saves, narrow the catalogue to repeated high-consequence errors. Keep custody and exact relation accounting even if a particular selection policy fails.

### Cold-clone paper: reconstruction and verification

Keep this operational. Demonstrate that a new checkout can recover the precise source, reconstruct a packet, find its returned bytes, and distinguish a compilation receipt from an exact-target admission.

A suitable replacement passage is:

> A cold clone should recover the evidence needed to interpret a result as well as the files needed to compile it. Packet manifests therefore refer to retained source objects rather than disposable worktrees. Arrival records bind returned material to the packet that elicited it. Verification receipts retain their evidence class, source version and target-check status.

The ZIP contains the full structures, replacement passages and bibliography entries for all three papers. The TeX has not been rendered as part of this return.

## 10. Wildcard: one bounded evidence-request phase

The fixed packet forces Type A to anticipate which omission will matter before Type B has read the task. A very large archive transfers that uncertainty to the reader.

Test one controlled relaxation: **after orientation, permit one batch of requests for pre-existing evidence**.

The reasoner supplies the parent packet digest, source IDs from an owner-approved catalogue, and a short explanation of why they are needed. The resolver returns only material allowed under the original target, cutoff, exclusions and budget.

It performs no fresh mathematical search, changes no target, accesses no personal connector, and accepts no arbitrary filesystem path. All additional bytes and reasoning costs count.

`query.py` implements that resolver.

This is a constrained active-retrieval design, not a claim to have invented active retrieval. Its leverage here is practical: the operator-mediated workflow can remain controlled while avoiding the requirement that the initial packet predict every relevant omission.

The first test should concern a missing definition or source span, not newly authored mathematical advice.

## Ordered next actions

1. **Capture the real loop before changing it further.** Retain the outstanding returns, exact packets, complete probe outputs and stranded branch versions. Deploy the custody projection so unassessed and unpropagated outputs remain visible.

2. **Correct the relation contract’s presentation.** Preserve the reverse proof currently discarded by `.isSome`; separate equivalence, sufficiency, strictness, nonvacuity and target supply. Run the four candidate Lean probes and admit a small independently reviewed relation set.

3. **Use the compiler for one actual round.** Start with the five audited distinctions, preserve mandatory context, keep the owner receipt separate, and capture every arrival against the dispatched packet hash. Judge this first deployment by reconstruction and assessment accuracy.

4. **Finish the appropriate existing results through the established path.** Recheck the live state of the stranded work and the merged-but-unpropagated endpoint. Preserve ordinary-proof, formal-proof and review distinctions while completing the required merge and paper updates.

5. **Run the matched comparison before expanding the machinery.** Use task families, a strong static brief, representation and failure-evidence interventions, and full cost accounting. Expand only the operations whose benefit survives that comparison.

**The result to aim for is one assessed distinction that keeps helping: it prevents a false completion claim, improves the next packet, survives as a regression case, and demonstrably reduces the cost or error of a later research round.**

so my point is you can do whatever a better version than any of the three individually, taking proper advantage of what we already have, ensuring it's all in the public repo, also all of the stuff we discoverd before all the issues that needs resolvin with each paper and each problem also do that, opus medium agents if its for reading, high if its for doing stuff, yeah please do all this and more
</pasted_content id="5348">
