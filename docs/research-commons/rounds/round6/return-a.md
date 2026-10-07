**The strongest move is to make Plectis improve the representation and context in which research is attempted, while using checked relations to keep the underlying question fixed.**

The corpus’s equivalent formulations, stronger sufficient conditions and failed arguments are valuable material for that system. They provide alternative ways into a question, tests of whether a reasoner has preserved its meaning, and evidence about which prerequisites an earlier method lacked.

There is also a structural error in how we have been judging the abduction work. Correcting it changes the direction substantially:

> **An engine that certifies a replacement by proving \(R\to H\) cannot produce a strictly weaker hypothesis than \(H\), in the same context. When it also proves \(H\to R\), it has established equivalence.**

That is the contract the supplied engine implements. Its tendency to produce equivalent or stronger conditions is therefore partly built into its acceptance criterion. My previous recommendation to expand that engine’s analytic reach left this distinction insufficiently central.

I would now build a **research-state compiler**: a system that maintains one research question through several checked representations, constructs an appropriate context for the next reasoner, and learns from what that reasoner actually does.

:chatgpt-content-reference{index="13"}[**Download the round-6 return: implementations, source findings, Lean candidates, tests, examples and paper revisions**](sandbox:/mnt/data/plectis_round6_return.zip)

The return contains **52 new passing Python tests and 23 passing tests from the supplied native suites**. It includes two generated, source-bound example packets and an executed query against the existing graph machinery. The Lean candidates are **uncompiled**. The reader experiment is explicitly **unrun**; its report records 72 `NOT_RUN` jobs, with unknown outcomes and costs.

## 1. What the infrastructure should become

Type A’s reading is substantially right: the useful infrastructure surrounds the reasoning process. The latest packet explicitly moves the problems into the role of test data and asks for the infrastructure around the deep corpus. It also reports 642 groups of mutually implying open statements and 627 bundles that restate their endpoints. Those are the relevant raw materials, rather than another invitation to concentrate on #249. :chatgpt-content-reference{index="0"}

But **“the infrastructure is the loop” is still too loose to determine what to build**. A loop can faithfully repeat an ineffective operation.

The maintained object should be:

\[
\boxed{
\text{a scoped research question}
+
\text{its alternative representations}
+
\text{the relations between them}
+
\text{the evidence from attempts}
}
\]

A packet is one compiled presentation of that object. A returned proof, counterexample, failed attempt or corrected interpretation updates it. The update must affect subsequent selection of representations, evidence or work.

This gives the existing components a clearer purpose.

The short paper identifies the current question and established conclusions. The long record preserves alternative routes and their histories. Lean owns exact mathematical relations. Comparator and the claim machinery check what the public account is entitled to say. The route record explains what was attempted and why it stopped. The packet builder chooses which parts the next reasoner needs. The experiment lane determines whether those choices help.

The three papers already acknowledge that the workflow’s comparative benefit is untested. That admission should become the next executed experiment, rather than remain a limitation repeated across successive papers. :chatgpt-content-reference{index="1"}

### What I would retain, freeze and remove

**Retain the formal corpus, its checked relations, the short papers, the failure history, and the existing verification and publication boundaries.** A formulation that has not yet helped another proof can still be a useful alternative representation or experimental control.

**Freeze further broad abduction expansion and dormant layers whose outputs have no exercised consumer.** They should return to active development when a measured episode identifies a specific missing capability. The same rule applies to further outreach preparation: prepared capacity and exercised capacity are different evidence classes.

**Remove false or stale assertions from active navigation and summaries once their source mismatch is confirmed.** Preserve their historical versions with an explicit superseding record. Erasing the earlier claim would discard the very failure history this infrastructure should learn from.

The packet’s account of the #1041 claim surviving in unregistered research prose is important here. A claim registry can be correct while the material supplied to the next reasoner remains misleading. The research-context boundary must therefore include the prose that retrieval and packet construction actually expose. :chatgpt-content-reference{index="2"}

## 2. Two findings that change the design

### The slot-replacement engine has a logical ceiling

The pending engine’s `restateScoped` constructs a proof of

\[
\Gamma\vdash R\rightarrow H,
\]

where \(\Gamma\) is the permitted context before the hypothesis being changed.

Its `weaker` test attempts

\[
\Gamma\vdash H\rightarrow R.
\]

Consequently:

| Evidence obtained | What it establishes |
|---|---|
| \(R\to H\) | A sufficient replacement, at least as strong as \(H\) under \(\Gamma\). |
| Both directions | Equivalence under \(\Gamma\). |
| Forward proof, reverse search fails | Sufficiency with an unresolved converse. |
| Forward proof plus an admissible separating witness | Strict strengthening, when the witness establishes the required separation. |

A failed reverse search is **not** a proof of strictness. Nor does the presence of a valid implication establish that its premises are satisfiable.

This concerns **one slot in its actual context**. The full source theorem and reconstructed theorem require their own comparison; their relationship cannot be inferred by counting changed binders.

For genuinely broader access to an endpoint \(G\), the relevant contract is instead

\[
\Gamma\vdash R'\rightarrow G,
\]

without the requirement to reconstruct the old intermediate hypothesis \(H\).

The architectural consequence is immediate: **use the current abducer as a generator of candidate representations and sufficient interfaces. Stop judging its slot output as though it were intrinsically a strict-weakening engine.** Endpoint improvement remains a separate operation and evidence class.

The exact source spans and the deduction from them are retained in :chatgpt-content-reference{index="14"}[the source findings](sandbox:/mnt/data/plectis_round6_return/SOURCE_FINDINGS.md).

### A real report changes the apparent mathematical meaning

The round-6 yield report contains this entry for `exists_upperHalf_boolean_word_of_boolean_suffix`:

```text
H: ∀ {n : ℕ}, 0 < n
R: True
weaker: True
```

The source theorem has the earlier hypothesis

```lean
(hk : k < n)
```

before

```lean
(hn : 0 < n)
```

So removing `hn` is valid in that context: `hk` already supplies positivity.

But the independently closed display

\[
\mathrm{True}\rightarrow\forall n:\mathbb N,\;0<n
\]

is false.

The engine checks a contextual contract, while the report closes the displayed hypothesis and residual over different sets of binders. **This is a reporting defect, not evidence of a Lean soundness failure.** It demonstrates why statement identity alone is insufficient for the proposed atlas.

The return includes a source-matched patch that retains both directions under **one complete telescope**, checks them separately and exports their contract identities and full contextual displays. Legacy displays remain for compatibility, explicitly distinguished from the actual comparison endpoints.

The patch retains proof values for checking inside the engine. Durable declaration admission still belongs to the existing replay/admission owner; printed contracts are not serialised proofs.

## 3. Turn the reformulations into a controlled space of representations

The central design needs **two distinct orderings**.

### Logical ordering: what follows from what?

Under a fixed foundation and compatible context, record checked implications, equivalences and separating witnesses.

Equivalent formulations count as **one question for progress accounting**. A bundle equivalent to its endpoint also counts as that endpoint restated, even when none of its individual members is equivalent to it.

This prevents the system from treating a new wrapper, rearranged quantifier or renamed conjunction as another mathematical advance.

### Operational ordering: which representation helps this method?

Keep the individual formulations available.

A formulation can be equivalent to another and still expose a more useful induction variable, a finite certificate, a construction interface, a filter statement or a theorem name that retrieval recognises.

Its value is then measured through:

\[
\text{representation}
+\text{method}
+\text{available context}
+\text{budget}
\longrightarrow
\text{observed outcome}.
\]

Equivalence does not imply equal search cost. Conversely, lower search cost does not imply stronger mathematics.

**Use the logical quotient for truthful accounting, while retaining the unreduced representations for search.**

This is where the apparent waste becomes an asset. The same collection can support proof transport, representation selection and controlled reader experiments.

### The transport rules are asymmetric

Given a checked implication \(A\to B\):

- a proof of \(A\) transports to \(B\);
- a refutation of \(B\) transports to a refutation of \(A\);
- failure to prove \(A\) says nothing comparable about \(B\).

These rules must preserve parameters and witnesses. A theorem about some independently chosen witness cannot silently discharge a demand about the witness already fixed by the consumer.

A stronger sufficient condition can therefore be a useful search target, even though proving it would not demonstrate a weakening. But repeated failure on that condition must not become a permanent prohibition on the endpoint.

### The resulting multiplication is concrete, but unmeasured

One checked relation can be reused in several ways. It can transport a later proof, prevent duplicate credit, identify a leaking benchmark split, expose an alternative working representation and invalidate an incorrectly scoped claim.

Similarly, one properly scoped counterexample can rule out several proposed routes that share its assumptions. A failed attempt with an identified missing prerequisite can become relevant again when another part of the corpus supplies that prerequisite.

That is a plausible multiplicative benefit from the existing material. **The number of classes does not establish the size of the benefit.** The experiment must show that sharing these relations and histories reduces repeated work or improves subsequent outcomes.

## 4. Use the native machinery rather than build another analyser

The supplied `argument_graph_frontier.py` already answers joint questions. It follows reductions and conditional refutations under assumed bundles, identifies joint endpoint equivalence, and searches for a cheapest cut within a caller-selected pool.

Its answers deliberately say:

```text
evidence_class: derivation_over_recorded_edges
satisfiability: not_established
```

That is the correct distinction. A graph derivation can identify a promising formal reconstruction without itself being a newly checked Lean proof.

I exercised that owner on the supplied older graph archive. It found both directions between `DemandLedger.G102` and the #249 endpoint, with the named witnesses:

```text
DemandLedger.Bridge1.Bridge1.irr_of_G102
DemandLedger.Bridge1.Bridge1.G102_of_irr
```

Both declarations are present in the supplied Lean source. The return includes the graph output and an **uncompiled seeded Lean probe** that packages those existing directions.

This run uses the older archived `g0` graph. It is **not** an update to the packet’s main-source 642-class census.

The useful next operation is to make those existing answers shape packets, return interpretation and work selection. A second implication engine would add another consistency burden.

### What the proposed layer returns on actual rows

| Source item | Correct interpretation | Next operation |
|---|---|---|
| The Boolean-suffix `hn` change | Contextual redundancy; the independently closed display is misleading. | Re-export the common telescope and retain the actual comparison. |
| `G102` and the #249 endpoint | Existing graph derivations establish both directions over recorded edges. | Treat them as views of one question; reconstruct the relation in Lean when a kernel certificate is needed. |
| Replay **B07** | A repeated-tail attempt stopped for stated reasons. | Record its unmet prerequisites; reconsider when a relevant capability changes. |
| Replay **B18** | A function-theoretic route was outside the recorded attempted support. | Run a new experiment; do not invent its historical outcome. |
| Replay **D09** | Certain method names were absent from five specified files. | Preserve that limited search observation; do not infer that the method is globally absent or impossible. |

The adapter reads **all 70 route rows**. Only **20 have a phrase anchor**. It preserves every classification as a reader classification and admits **zero new kernel relations** from those labels.

This is also the right treatment of the false #1041 “complete proofs”. The supplied record says ten such returns were rejected at missing steps. Those failures are valuable labelled examples, but their claimed implications cannot simply be promoted into a checked collection. The missing step, actual formal statement and eventual counterexample must remain distinguishable. :chatgpt-content-reference{index="3"}

## 5. Compile the next reasoner’s context around the distinctions it must preserve

A large packet can contain the right information and still fail to make the decisive distinction visible.

For this corpus, the packet builder should ask:

> **Which source fragments must remain together so that the next reader can distinguish the intended question from the nearby wrong interpretations and unsuitable routes?**

The registered distinctions might include a contextual implication versus its independently closed display; a failed attempt versus a proved obstruction; a sufficient condition versus the endpoint; or an exact counterexample versus an informal negative intuition.

The implementation in `contrast_packet.py` uses a finite, explicit specification:

```text
task and intended-question anchor
source identities
byte budget
mandatory context
registered contrasts
source fragments with dependencies and provenance groups
```

It closes mandatory fragments under their declared dependencies. If that material exceeds the budget, it refuses the packet rather than truncating the guard. It then selects further dependency bundles by newly covered contrasts per additional serialised byte.

The output records precisely what was covered and what remains missing.

This is a **deterministic heuristic**, not an optimality claim. Its guarantee is restricted to exact bytes, declared dependencies, exclusions and the registered contrasts. It does not certify that an arbitrary research task has received all necessary mathematics. Constructing and reviewing the contrast set is itself work to measure.

### Two examples are built

The return contains a **3,426-byte packet** over B07, B18 and D09 that preserves four registered distinctions, and a **2,255-byte packet** containing the Boolean-suffix report and its actual source telescope.

These are narrow, seeded examples. Their sizes are not a compression ratio against the complete round-6 working archive, and they do not establish improved reader performance.

For historical experiments, use the existing `build_benchmark_packet.py` source-cut owner. It already provides relevant controls and recognises leakage risks. The new selector belongs inside that preparation path.

In particular, the present round-6 packet contains later replay outcomes. Removing a paragraph headed “result” does not turn it into an uncontaminated historical packet.

## 6. Keep every return, without confusing custody with acceptance

There are four separate decisions:

\[
\text{capture}
\quad\rightarrow\quad
\text{formal validity}
\quad\rightarrow\quad
\text{intended-question fidelity and usefulness}
\quad\rightarrow\quad
\text{publication}.
\]

They should not be collapsed into one gate.

Capture every return immediately, including incorrect ones. Retain exact input and output bytes, native probe or review artefacts, and their source identities. An expiring CI artefact should not be the only surviving copy.

A valid conditional theorem can be retained even when it does not beat a baseline or its nonvacuity remains unknown. Requiring every conditional interface to prove its own premises satisfiable could force the system to settle an open existence question merely to preserve a useful conditional theorem.

On the other hand, a valid proof of an unintended statement must not receive credit for the intended question.

The returned `episode_replay.py` provides immutable content-addressed custody and chain verification. It is an implementation leaf for existing intake and receipt machinery. **A hash proves byte identity, not mathematical truth, authentic review or historical availability.**

The native `accept_research_return.py`, route-receipt and proof-workbench owners remain authoritative. An existing durable store should replace the candidate store wherever it already meets the requirement.

## 7. The experiment should test the proposed interaction

The strongest evaluation does not ask only whether an agent eventually proves more original conjectures. It asks whether the maintained record helps a reader make a correct, useful continuation.

There are two levels.

**First, semantic and navigational controls.** Can a fresh reader preserve the question, recognise the exact scope of a relation, distinguish a stopped method from an impossibility result, and select a justified next operation?

**Second, actual research continuation.** Does the selected representation and history help the reader produce a checked useful contribution or avoid a demonstrably inappropriate route, after including the cost of preparation and review?

The first level can use existing certified relations without solving the open endpoints. It must not be advertised as autonomous theorem discovery.

### Use the careful static briefing as the principal control

The strategy paper already proposes raw repository, careful static briefing and navigation conditions. Keep that comparison.

Then cross two factors:

| | Failed-route evidence withheld | Failed-route evidence available |
|---|---|---|
| One canonical representation | \(Y_{00}\) | \(Y_{01}\) |
| Multiple certified representations | \(Y_{10}\) | \(Y_{11}\) |

The interaction

\[
Y_{11}-Y_{10}-Y_{01}+Y_{00}
\]

tests whether representations and route history complement one another for the chosen outcome.

A positive interaction is something to measure. It is not warranted merely because the design combines two useful-looking components.

Block by question and provenance family. The 103 members of one equivalence class are not 103 independent research problems. Keep model, engine, foundation and permissible information fixed; repeat stochastic runs and randomise presentation order.

Charge preparation, retrieval, failed proposals, checking, repair and review. Library-learning evaluations have shown why this matters: apparent gains in the systems studied by Berlot-Attwell and colleagues weakened or disappeared under matched computational accounting, and library presence did not establish actual reuse. Those findings concern their evaluated systems rather than a general impossibility of library learning. :chatgpt-content-reference{index="4"}

### Mathematical transport does not authorise outcome transport

Dream-RSI makes recorded exploration histories reusable for policy evaluation while holding the underlying discovery agent and evaluator fixed. Its replay reveals recorded outcomes from the explored tree. :chatgpt-content-reference{index="5"}

Plectis has an additional temptation: a proved equivalence can make two questions mathematically interchangeable, so the system may assume that a recorded attempt on one provides an outcome for the other.

It does not.

Changing the representation, premise set or supplied history can change the generated attempt. That branch requires a new observation. The return’s evaluator rejects an unobserved `out_of_support` branch carrying a fabricated correctness result.

The included experiment plan consequently reports **72 `NOT_RUN` jobs**, rather than assigning zero success, zero cost or simulated discoveries.

## 8. What the literature already has, and what remains worth testing

Several components of this design have strong precedents. The paper should engage them directly.

**The Equational Theories Project is a substantial predecessor to an implication atlas.** It combines formal implication and non-implication results, equivalence classes, multiple proof and countermodel techniques, and source-derived interfaces. Its paper also describes using those interfaces while the graph was incomplete. Dismissing it as merely a finished finite benchmark would miss the relevant infrastructure. :chatgpt-content-reference{index="6"}

**Prove2Me and Formal Conjectures already address statement fidelity.** Prove2Me separates immutable statements from proofs and includes independent statement read-back and human auditing. Formal Conjectures uses proof and disproof attempts, test lemmas and review to expose misformalisations, with frozen evaluation versions. Plectis should inherit those distinctions rather than claim that checking intended statements is its invention. :chatgpt-content-reference{index="7"}

**TheoremGraph already provides statement-level formal/informal retrieval infrastructure.** Its graded extraction and matching evidence are useful for selecting candidate context, but should not be promoted into a checked implication. :chatgpt-content-reference{index="8"}

**TWITCH and ProofEvolve already make failed or partial proofs productive.** TWITCH learns abstractions from failed partial proofs and successful proofs; ProofEvolve retains verified schemas and recombines them with explicit residual obligations. Persistent partial-proof reuse is therefore a baseline, not an available broad novelty claim. :chatgpt-content-reference{index="9"}

**Equivalent-variant evaluation also has prior art.** PutnamGAP explicitly evaluates robustness across mathematically equivalent variants. A new benchmark of reformulations alone would not establish the proposed infrastructure contribution. :chatgpt-content-reference{index="10"}

The research hypothesis worth pursuing is the **coupled behaviour**:

> Checked contextual relations govern credit and proof transport; alternative representations govern measured search; failed-route evidence shapes packet construction; and actual outcomes improve the next context-selection decision.

The literature examined does not establish that Plectis already performs this operation better. Nor does it justify saying that no other system could contain a similar combination. The useful claim to earn is an executed one: **this maintained structure changed what the next reasoner could correctly and usefully do, beyond an information-equivalent static briefing.**

The Aletheia evidence makes that test consequential. In the reported December-2025 study, human reviewers judged 63 of 200 definitively assessed candidates technically correct, but only 13 as addressing the intended problem. The remaining 50 demonstrate the importance of fidelity in that study; they are not a universal error rate for AI mathematics or a Lean benchmark. :chatgpt-content-reference{index="11"}

## 9. The three concrete builds

The ZIP provides complete code for three coupled implementations, plus the Lean reporting patch and canaries.

| Build | Returned implementation | Native integration |
|---|---|---|
| **Contextual semantic projection** | `atlas_projection.py`, `patch_scoped_export.py`, full patched engine/export files, `AtlasContracts.lean`, existing-relation probe | Extend slot export and the existing route/question views. Reuse the native frontier and relational evaluator. |
| **Contrast-preserving packet selection** | `contrast_packet.py`, `make_examples.py`, complete source-bound specifications and produced packets | Extend existing packet preparation and route queries. Preserve historical-source and holdout controls. |
| **Persistent episode capture and matched evaluation** | `episode_replay.py`, regression tests, experiment plan and unrun report | Attach to existing intake, native review receipts and experiment execution. Feed accepted changes into future packet/work selection. |

The core logical boundary in the Lean candidate is deliberately small:

```lean
structure SlotReplacement (Ctx : Sort u) (H R : Ctx → Prop) : Prop where
  reconstruct : ∀ c, R c → H c

structure EndpointRoute (Ctx : Sort u) (R G : Ctx → Prop) : Prop where
  reconstruct : ∀ c, R c → G c
```

`Ctx` carries the shared parameters and hypotheses. The canaries check why the first contract excludes strict weakening of its slot, why the converse establishes contextual equivalence, and why the flattened positivity display is invalid.

The Python return is reproducible with:

```sh
python -m unittest discover -s tests -v
python -m compileall -q code tests
```

The README supplies exact commands for the actual route projection, native graph query, example regeneration, custody and paired report. Regenerating the example packets and both patched Lean files produced byte-identical copies.

**Executed here:** 75 Python tests in total, the native graph queries and the packet-generation examples.

**Still requiring Type A:** compiling the Lean candidates under the pinned probe policy, connecting the adapters to the live owners, and running fresh readers. The first corpus export probe should be limited to the two named Boolean-suffix declarations; its 30-minute cap remains a cap, not a predicted completion time.

## 10. What the papers should say

The main paper should describe **a maintained research question and its continuation through different representations and reasoners**. One source-bound episode should organise the account.

Its structure should follow the actual operation: question and record; Type A/Type B loop; contextual relations; packet construction; returned work and adjudication; historical evidence; controlled evaluation; limitations and reproduction.

A replacement opening is:

> A research record contains more than the current theorem statement. It contains alternative formulations, arguments that stopped for different reasons, computations on bounded domains, counterexamples to particular generalisations and proofs whose published interfaces conceal useful facts. A later reader must determine which of these objects applies to the question now being asked.
>
> Plectis maintains this information alongside a formal development. The short paper presents the current conclusions and remaining obligations. The longer record preserves the routes by which the project arrived there. Lean declarations and comparison checks establish the exact statements supported by the formal development. The research loop selects part of this record for another reasoner, receives its proposed contribution, checks the contribution at the appropriate evidence level and incorporates the resulting change into future work.

The paper should distinguish three kinds of evidence: the historical record shows what happened; source-bound tests show specific mechanisms working; controlled reader experiments test whether the infrastructure caused an improvement.

There is a concrete correction to the current related-work discussion. Its broad statement that the graph records no jointly inconsistent sets needs to distinguish the existing joint-conflict query and local nogood use from a complete maintained collection of minimal inconsistent sets. The source supports the former, not the latter.

The strategy paper should become the companion on participation, exercised capacity and stewardship cost. Its existing careful-static-briefing experiment should move into execution.

The cold-clone note should retain its narrower technical role: pinned source, navigation and proof receipt. Its own audited snapshot must remain separate from later main-source counts, and a supported cold-clone procedure must remain separate from observed external use.

:chatgpt-content-reference{index="15"}[**The paper revisions file**](sandbox:/mnt/data/plectis_round6_return/paper/REPLACEMENTS.md) contains proposed structures and replacement abstracts and sections for all three papers. It keeps the proposed round-6 capability and unrun experiment distinct from the implemented public system.

## 11. Wildcard: make reader failures improve the context compiler

The additional change I would pursue is **counterfactual context repair**.

When a reader mishandles one valid representation but succeeds after receiving additional source context, investigate which dependency-closed context change corrected the decision.

The loop becomes:

\[
\text{observed interpretation failure}
\rightarrow
\text{small source-context intervention}
\rightarrow
\text{repeated reader test}
\rightarrow
\text{new packet-selection requirement}.
\]

This is more useful than adding another instruction saying “be careful about hypotheses”. It identifies the evidence that the reader needed to preserve the question.

The first case is already available. Compare the independently closed `hn` report with the exact theorem telescope and with a packet preserving the decisive `hk : k < n` context. Keep the reader policy fixed. Measure whether it correctly identifies contextual redundancy rather than claiming an unconditional positivity theorem or a strict mathematical improvement.

Then test the resulting selection requirement on held-out declarations.

A deletion-minimal context repair is not necessarily a uniquely necessary explanation. Several fragments may substitute for one another, and stochastic readers need repeated observations. The useful result is a measured, transferable improvement to packet construction.

**This would allow the system to improve its own reasoning interface from the corpus’s mistakes, while leaving the kernel and intended-statement review boundaries unchanged.**

## The integration decision

Type A should take the three builds as one coherent wave:

1. **Repair and expose the contextual relation boundary**, then connect it to the existing question and route projections. Reclassify slot outputs without discarding their representations.
2. **Use those projections to compile actual next-reader packets**, preserving the distinctions illustrated by the source-bound examples.
3. **Capture and execute the matched continuation experiment**, then spend its observed successes and failures on the next packet-selection change.

The previous return concentrated on making abduction more capable. This return changes the governing objective: **make the existing corpus more effective at presenting, preserving and continuing the right research question, and measure that effect.**

Type A should inspect the live owners first and use a stronger existing integration wherever the live repository supports one; the returned implementations are a tested starting point, not a ceiling.

**The next version of Plectis should learn which representation and evidence a research task needs, while keeping the task’s meaning fixed.** Its surplus of restatements supplies controlled variations of a problem. Its failed interpretations supply distinctions that later packets must preserve. Its verification machinery can establish which changes preserve meaning and which merely make a statement easier to prove.

The consequential change is to connect those three things: **a reviewed failure should change how the next research context is constructed**, rather than merely add another warning to the record.

