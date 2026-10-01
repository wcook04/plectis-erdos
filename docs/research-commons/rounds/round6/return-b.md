I have built the core of that design against the supplied material.

**:chatgpt-content-reference{index="17"}[Download the complete round-6 return](sandbox:/mnt/data/plectis_round6_return.zip)**

The ZIP contains the three implementations, tests, an archive-replay experiment, a context-preserving Lean export patch, generic Lean regression candidates, the evaluation protocol, replacement paper passages and ordered integration instructions.

| Work performed on the supplied bytes | Result |
|---|---|
| Python regression suite | **96 tests passed**, including exhaustive small-model checks, withholding guards, source integrity and concurrent custody |
| Formulation-class replay | **103 formulations**, represented by **204 directed tree edges**, reconstructing **10,506 structurally checked implication paths** |
| Source-bound packet compilation | One historical review task compiled into **4,494 UTF-8 bytes**, satisfying five explicit coverage obligations |
| Historical route import | All **70 rows** retained, without promoting their prose classifications to formal evidence |
| Export patch | Applies to the exact supplied pending files and reproduces the included candidate hashes |
| Lean and reasoner evaluation | **Not run here**; the Lean files are compilation candidates, and no performance improvement is claimed |

The graph experiment uses the older archived Lean tree `16acc13d…`, not the export underlying the round-6 brief’s 642-class census. The checks establish composition over the supplied graph’s reported rules, not fresh Lean admission. `SOURCE_AUDIT.md` records the precise source identities and review scope.

# 1. The verdict: build a compiler for research contexts

Type A’s diagnosis identifies the right operational centre. The supplied history associates useful results with aimed rounds, rereading the route record and subsequent formalisation. It also records substantial unfinished work between receiving a return and updating its consumers. The same audit records 374 returns, the successful September cohort, the repeated false-completion claims and work left outside durable custody. Those are grounds for redesigning the research loop. They are not yet evidence that packet construction or failed-route history caused the successful outcomes. :chatgpt-content-reference{index="0"}

I would revise the diagnosis in three respects.

**First, equivalent formulations are not failed contributions by definition.** They do not establish a new logical consequence merely by acquiring another name. They can nevertheless expose a witness, suggest a construction, remove an unhelpful encoding or make a later proof much cheaper. Their value belongs in an operational measurement.

**Second, failed attempts must remain distinguishable from proved obstructions.** “This argument cannot work under these assumptions” can be reusable mathematical evidence. “This model failed with this packet and budget” is an observation about an attempt. Treating the latter as the former would suppress precisely the exploration the record is supposed to support.

**Third, the useful object is larger than a theorem or a route label.** It is a source-bound research episode: what was asked, which formulation was exposed, what information was supplied, what came back, what was checked and which later consumer changed.

That leads to one integrated design, which I call the **contrastive research compiler**:

```text
Exact target and admissible context
    + alternative formulations
    + scoped failures and competing interpretations
    + the next consumer’s requirements
                         ↓
          Bounded, reproducible research packet
                         ↓
             Returned proposed change
                         ↓
       Independent review and proof verification
                         ↓
    Consumer dispositions and revised packet requirements
```

Here, a *contrast* is a specific distinction the reasoner must preserve: fixed parameters versus universal closure; independent witnesses versus a shared witness; a sufficient special case versus the original assertion; a failed attempt versus a refutation.

The system’s accumulated knowledge changes **the next input**, not just the archive.

## Build 1: a contextual contrast and route record

The full implementation is in `contrast_core.py` and `route_record.py`.

It records three separate identities:

| Identity | What must be preserved |
|---|---|
| Intended claim | Exact source passage, interpretation review and application domain |
| Formal formulation | Elaborated statement, ordered parameter context, admissible hypotheses and environment |
| Attempt | Actual formulation and packet exposed, source access, budget, returned bytes and outcome |

The core represents implications as rules requiring **all** their premises, retains alternative proofs and recomputes consequences from supplied facts. A conditional refutation remains conditional. An unseeded cycle establishes nothing.

It also builds compact transport paths between equivalent formulations. Those paths retain their side-premise evidence and are invalidated when their dependencies are withheld.

The route importer preserves all 70 historical classifications, but leaves missing formal anchors and scopes explicitly unfilled. This respects the original `replay_worlds/check_routes.py`: its own docstring limits it to checking classifications, declared occurrences and related record structure. It does not claim to verify the mathematics. The new importer extends that record rather than pretending an occurrence check already supplies semantic authority.

**Integration:** add the contextual records beside the existing argument graph, and expose them through `query_continuations.py`. Keep the existing historical checker. Do not create another independent route database with competing ownership.

## Build 2: a packet compiler that preserves necessary combinations

The implementation is `packet_compiler.py`.

The important departure from ordinary relevance ranking is that evidence often matters **jointly**. A definition without its counterexample can leave a misunderstanding intact. A theorem without its parameter scope can invite an invalid application. A supplier and its transport may be useless separately.

The compiler therefore represents each requirement as an **OR of AND groups**. This is an actual requirement from the returned experiment:

```python
Requirement(
    "show_direction_test_and_closure_together",
    (
        frozenset({"reverse_probe", "closure_code"}),
        frozenset({"full_engine"}),
    ),
    kind="joint_context",
)
```

Either supply both short excerpts, or supply the larger excerpt containing the required context. Selecting only the more “relevant” short excerpt does not satisfy the requirement.

For a chosen formulation \(v\), the optimisation is:

\[
\min_F \operatorname{cost}(F)
\quad\text{subject to}\quad
\forall d\in D(v),\ \exists j,\ A_{d,j}\subseteq F.
\]

Here \(F\) is the selected source material, and each \(A_{d,j}\) is an acceptable evidence group. Shared excerpts are charged once.

The implementation performs bounded branch-and-bound over these groups. A completed search establishes an optimum **within the declared finite coverage model**. An interrupted search is labelled incomplete. An impossible budget produces explicit uncovered obligations or a bounded-model failure explanation.

It does not claim that the selected packet is the globally best prompt, or that supplying a distinction guarantees a model will understand it.

**Integration:** put this selection step before `type_b_handoff_bundle.py`. Retain the existing packaging machinery; replace worktree-dependent manual selections with immutable, auditable source selections.

## Build 3: custody tied to consumer completion

The implementation is `round_store.py`, with `examples/open_review_round.py` providing a usable entry point.

The packet must enter durable custody **before delivery**. The return enters custody before interpretation. Review and validation are separate events. Every required consumer then receives an explicit disposition.

That directly addresses the recorded failure in which round-5 returns existed in Downloads and a temporary scratchpad without a batch entry. The source also records older manifests pointing into deleted worktrees and recent batches remaining open. :chatgpt-content-reference{index="1"} :chatgpt-content-reference{index="2"}

The meaningful completion condition is:

> Every required consumer has been updated, verified unchanged, marked inapplicable with a reason, or deferred with an owner and a discriminating re-entry condition.

“Copied into the repository” is not that condition.

The code provides content-addressed bytes, locked append operations, duplicate-delivery idempotence, integrity checking and an inert custody archive. A revised review invalidates earlier dependent consumer dispositions and validation records.

**It does not grant mathematical authority to a JSON receipt.** Type A’s independent proof and source-review process remains necessary.

Integration belongs in the existing return-intake and coverage-ledger owners. There should be no additional global task inbox.

The returned code can be exercised with:

```sh
python3 -m unittest discover -s tests -v

python3 scripts/reproduce.py \
  --review-root /path/to/r6_review \
  --out /path/to/empty/replay

python3 examples/open_review_round.py \
  /path/to/empty/replay/compiled_packet \
  /path/to/new/round_store
```

The last command retains the learner ZIP and its manifest. It sends nothing.

# 2. Turning the restatements into useful infrastructure

The round-6 record reports 642 disguise classes, a largest class of 103 formulations and 627 bundles marked as restating their target. Those numbers describe an unusually substantial collection of alternative presentations within this corpus. They are not, on their own, counts of discoveries. :chatgpt-content-reference{index="3"}

The useful transformation is to make that collection support **controlled semantic changes and controlled operational experiments**.

## A. Preserve the parameter context or the comparison can become meaningless

This is the most important correctness condition for the proposed progress gate.

Consider the historical growth replacement. For a fixed function \(c:\mathbb N\to\mathbb N\), write

\[
H(c)\equiv \forall m,\ c(m)\leq m,
\qquad
R(c)\equiv \forall m,\ c(m)\leq0.
\]

The historical export contains precisely this kind of replacement. :chatgpt-content-reference{index="4"}

Clearly \(R(c)\Rightarrow H(c)\). But \(c(m)=m\) satisfies \(H\) and violates \(R\). Thus **the replacement is strictly stronger on the original parameter scope**.

Now compare the separately closed propositions:

\[
(\forall c,\ H(c))
\qquad\text{and}\qquad
(\forall c,\ R(c)).
\]

Both are false: take the constant-one function and evaluate at \(m=0\). Consequently they are equivalent, for a reason that tells us nothing useful about replacing the hypothesis of the original theorem.

A naïve equivalence gate consuming only independently closed display strings could therefore call a harmful strengthening an equivalence.

The correct object is

\[
\forall\theta,\ \Gamma(\theta)\to
\bigl(R(\theta)\to H(\theta)\bigr),
\]

with the reverse direction checked under the **same** parameters and admissible background.

The candidate Lean definitions make the distinction explicit:

```lean
def Entails {α : Type u} (Γ P Q : α → Prop) : Prop :=
  ∀ x, Γ x → P x → Q x

def Separates {α : Type u} (Γ P Q : α → Prop) : Prop :=
  ∃ x, Γ x ∧ P x ∧ ¬ Q x

structure StrictStrengthening
    {α : Type u} (Γ old new : α → Prop) : Prop where
  sufficient : Entails Γ new old
  lost : Separates Γ old new
```

**An important correction to avoid wasting Type A’s time:** the supplied pending engine already performs its reverse attempt in the preceding scope. It also guards insertion of ordinary graph reductions with a closed-contract check. I am not alleging that it currently makes the unsound comparison above.

The actual loss is narrower: the exporter retains separate closures and a Boolean, while discarding the reverse proof and much of the shared comparison context. The included patch preserves that evidence without weakening the existing guard. Exact loci and base hashes are in `SOURCE_AUDIT.md` and `patches/BASES.json`.

## B. Replace “weaker” with the directions actually established

The current export reports 103 changed slots: three given slots and 100 restated slots, with `abduction_slots_weaker = 3`. The counter excludes the given slots. :chatgpt-content-reference{index="5"}

That needs a more careful interpretation than “three improvements”.

If the system has already checked \(R\to H\), and its reverse search also proves \(H\to R\), it has established **equivalence in that scope**. A failed reverse search establishes neither strictness nor non-equivalence.

The reported second-channel rewrite illustrates the difference. Its arithmetic shape is

\[
\frac16+\frac{37}{56}t\leq |u-\tfrac13|
\]

versus

\[
t\leq \frac{56}{37}|u-\tfrac13|-\frac{28}{111}.
\]

These are equivalent by elementary linear rearrangement. Yet the machine-yield record gives the corresponding row `weaker False`. That is evidence that the bounded reverse test did not establish the direction, not evidence that the direction is false. The exact row and generic Lean regression candidate are included in the return.

The gate should report:

```text
forward implication: accepted / unknown
reverse implication: accepted / unknown
strictness: separating instance / unknown
feasibility: witness / refutation / unknown
intended-source correspondence: reviewed / unresolved
operational benefit: measured / unmeasured
```

These fields answer different questions. Compressing them into one “progress” flag would recreate the current confusion.

## C. Distinguish a narrow condition from a vacuous one

The current record includes

\[
r<\operatorname{mersenneTail}(m)
\quad\rightsquigarrow\quad
r\leq0.
\]

The supplied trace records this as an unhelpful strengthening. :chatgpt-content-reference{index="6"}

Under a positive tail \(T\), the condition \(r\leq0\) is sufficient for \(r<T\), and it is feasible: \(r=0\) works. It nevertheless removes positive values of \(r\) that satisfy the original condition.

For a consumer specifically requiring \(0<r\), the replacement becomes inconsistent with the application domain. Without that requirement, it is simply a narrow sufficient slice.

That is why the application domain belongs in the record. Otherwise the system will alternate between overclaiming progress and incorrectly rejecting valid special cases as “vacuous”.

The same distinction matters when interpreting the Aletheia evidence. Its study found 63 technically correct responses among 200 definitively graded candidates, but only 13 addressing the intended question. The remaining 50 concerned unintended readings, which were not necessarily false-premise vacuity. Those are measurements from that particular study, not an established failure rate for Plectis. :chatgpt-content-reference{index="7"}

## D. Reuse proof relations across a family, but never copy performance labels

For a strongly connected class of \(k\) formulations, choose a representative and retain:

- a directed tree reaching every member from the representative;
- a directed tree returning every member to it.

There are \(2(k-1)\) tree edges. Any member-to-member implication is reconstructed through the representative, with its side-premise proofs retained.

For the archived 103-member class, the returned implementation constructs **204 edges** and checks all **10,506 ordered non-reflexive pair certificates**.

This is a genuine reuse mechanism. One checked relation or appropriately scoped separating instance can serve many presentations. It is also an established graph construction, not a new mathematical foundation.

The crucial boundary is:

> **Logical evidence can transfer along checked relations. A model’s failure, runtime and success probability cannot.**

A failed attempt on formulation \(P\) does not imply failure on equivalent \(Q\). Indeed, testing that difference is one of the main uses of the class.

This gives Plectis a way to investigate representation sensitivity without changing the underlying task. It also supplies a principled evaluation unit: **the 103 formulations are one family, not 103 independent problems or 10,506 independent successes.**

## E. Make a rejected interpretation alter the next packet

This is the part that converts the negative history into a continuing benefit.

Suppose Type A rejects a return because it treated independently chosen witnesses as one common witness. The record should retain the exact proposed statement, the intended statement, their shared scope and the evidence separating them.

The subsequent packet compiler receives a new obligation:

> Supply an evidence group that makes the independent-versus-shared witness distinction inspectable.

That obligation may be satisfied by a definition plus a counterexample, a formal statement plus its quantifier explanation, or another reviewed source group. The compiler chooses among these under the budget.

The same correction can then be attached to other formulations through checked relations. It should not have to be rediscovered under each new name.

**The feedback is a change in future input construction.** A warning that remains buried in an archive has not completed that operation.

This must remain review-controlled. A failed attempt does not automatically become a universally valid exclusion rule. The system should preserve an explicitly budgeted route for exploring alternatives that its current classification does not anticipate.

## What the packet experiment actually demonstrates

I compiled a review packet for the historical `summable_coeff_term` growth replacement. Its obligations were to preserve the original parameter binding, show the exact proposal, show the reverse test together with closure logic, identify the comparison scope and include the existing closed-contract guard as contrary evidence against a mistaken diagnosis.

The compiler selected six short source blocks in **4,494 bytes**, including the task header. The seven candidate blocks, including a larger alternative, totalled 10,027 bytes.

The requirements were authored and auditable. This is **not** a claim that the entire 104 MB corpus can be replaced by 4 KB, or that a reasoner performed better with the packet. It establishes that a useful small task can be assembled reproducibly while preserving specified combinations of evidence.

The implementation also checks required anchors within a selected source span. A correct whole-file hash does not prevent accidentally selecting the wrong lines of that file.

# 3. The literature sets a higher bar than another implication graph

Several proposed components already have close precedents. The design should use them accurately and test the additional combination.

| Precedent | What Plectis must acknowledge | Increment to test |
|---|---|---|
| **Equational Theories Project** | A large Lean-validated implication and non-implication structure, with equivalence classes and compositional reuse. | Context-dependent research formulations coupled to packet construction and later consumer effects. :chatgpt-content-reference{index="8"} |
| **BEq+** | Constrained bidirectional comparison of formal statements; it explicitly identifies the problem of unrelated true statements passing unrestricted equivalence tests. | Shared-telescope evidence, scoped separators and interpretation contrasts feeding subsequent packets. :chatgpt-content-reference{index="9"} |
| **Prove2Me** | Immutable proof-sketches with open dependencies, attested source milestones, reuse and cross-agent correction. | Bounded contrast-covering contexts and controlled interventions on the research record. :chatgpt-content-reference{index="10"} |
| **ProofEvolve and Twitch** | Persistent checked partial structures, or abstractions extracted from proofs and failed attempts, with reuse evaluations. | Selection of a research presentation and its evidence under a fixed semantic anchor. :chatgpt-content-reference{index="11"} |
| **Dream-RSI and TheoremGraph** | Recorded-outcome replay and structured mathematical retrieval. | Preserve the distinction between transported logical evidence and fresh performance measurements; select complementary evidence groups. :chatgpt-content-reference{index="12"} |
| **LeanFlow** | Source-reviewed statement skeletons and controlled workflow ablations. | Isolate the additional effect of contrast-driven packet construction while holding review and proof workflows fixed. :chatgpt-content-reference{index="13"} |

TheoremGraph’s own results make the conjunction issue particularly relevant: a configuration improving concept retrieval degraded chained-premise retrieval. Retrieving individually similar statements and retrieving a jointly useful proof context are different tasks. :chatgpt-content-reference{index="14"}

The defensible research claim is therefore specific:

> Plectis constructs and revises a reasoner’s information environment using exact formulation relations, reviewed interpretation contrasts and recorded consumer requirements, then measures the consequences under controlled exposure.

The sources reviewed do not justify a universal claim that no existing system combines these ideas. Nor does this structural prototype establish superiority. **The contribution to pursue is the verified integration and its measured effect**, not the naming of familiar components.

# 4. The experiment that would establish the value of the record

The key experiment should ask:

> With the intended task, model, accessible sources and total resource policy held fixed, does the compiled context improve the next consumer’s verified outcome?

Historical associations cannot answer that. A larger graph cannot answer it. Unit tests cannot answer it.

## Separate presentation from history

Use a strong Type A hand-authored packet as the primary baseline. It should contain the history and navigation support Type A would actually provide.

Compare that with the existing structured retrieval route, a compiled packet using a fixed formulation, and a compiled packet allowed to choose among certified formulations.

Within the compiler conditions, separately withhold reviewed failed-route history and disable contrast-coverage constraints. This distinguishes the value of the proposed mechanism from simply having more source material.

All variants of one formulation family must remain together in the train/test split and in uncertainty estimates. Fresh learner contexts should prevent one arm’s discoveries leaking into another.

## Measure useful avoidance and useful reopening

A good system should avoid a **proved impossible step under its recorded assumptions**. It should not prohibit a new attempt merely because a previous model timed out.

Include both cases. Otherwise a conservative system can appear successful by suppressing all difficult research.

Likewise, include a distinct second-generation consumer. Generation one supplies a verified relation or interpretation correction. Generation two receives a revised packet because of it. Record whether the correction was actually used and whether the promised consumer artifact changed.

The measurement is then about the record changing subsequent work, rather than a file being present in a prompt.

## Charge the whole operation

Include model calls, context, retrieval and packet construction, Lean execution, formalisation repair and human review. Separate one-off construction costs from amortised costs.

Compute-aware library-learning evaluation explicitly requires attention to these costs and to actual reuse behaviour. More stored material does not by itself demonstrate a useful learning effect. :chatgpt-content-reference{index="15"}

The first pilot can be small and preregistered. `EXPERIMENT.md` proposes beginning with a modest set of independently reviewed families, conditional on the source inventory supporting them, then estimating variation before expanding.

A negative result must remain possible: the best manual packet may outperform the compiler.

## Strict withholding is not ready in the bundled graph

A source-withholding test needs complete transitive **type and value dependencies**. It must recompute supplied facts and formulation classes after masking. A transport proof depending on a withheld endpoint cannot remain in the evaluator’s evidence.

The archived graph lacks the complete footprints required for that test. The returned code therefore fails closed under a strict nonempty mask. The included mask diagnostic is synthetic and is labelled as such; it is not a causal donor-withdrawal experiment.

The missing dependency evidence is a concrete next implementation requirement, not a reason to substitute an unsupported claim about what the corpus could or could not prove.

# 5. The systems paper

The paper should lead with the actual research episode: **a fixed packet leaves the corpus, a return proposes a change, that change is checked and followed into its consumers, and the next packet changes accordingly**.

The existing verification and publication machinery remains important. It should explain how this operation remains faithful, rather than displace the operation from the centre of the paper.

The proposed structure is:

| Section | Purpose |
|---|---|
| A research episode | One complete, source-bound example with the remaining obligation explicit |
| Claims, formulations and attempts | Define the objects and the Type A / Type B relay |
| Contextual relations | Implications, scope, strictness, feasibility and formulation families |
| Preparing the next packet | Coverage groups, selection, source identity and exposure |
| Receiving and integrating a return | Custody, independent review and consumer disposition |
| Evidence | Historical ledger, structural pilot and the controlled experiment when completed |
| Related systems and limits | Direct comparisons and the exact evidential boundaries |

`paper/RESTRUCTURE.md` maps this onto the current section labels and line numbers. The ZIP includes concrete LaTeX replacements. These are the principal passages.

### Proposed opening

> Plectis maintains a source-bound record of mathematical research and uses that record to prepare subsequent research tasks. The record connects a source statement to its formal formulations, conditional arguments, failed attempts, verification evidence and public claims. Research proceeds between a corpus-resident agent, which can inspect and change the working tree, and a reasoner receiving a fixed packet of information. The former verifies and integrates returned material. The packet determines which parts of the research record are available to the latter.
>
> The operation we study is the preparation and revision of that context. Equivalent formulations provide alternative presentations of the same obligation. Conditional reductions expose the premises still required by an argument. Counterexamples and rejected interpretations identify distinctions that later packets need to preserve.

### Proposed capability passage

> A reviewed correction can add a coverage obligation to the next packet. The correction must identify the competing reading, the distinction that was lost and the evidence that makes that distinction inspectable. In this way, a failed interpretation can change subsequent input construction even when it contributes no new theorem.

### Proposed evidence passage

> On an older archived graph, a local replay recovered a family of 103 formulations and constructed a 204-arc transport basis. All 10,506 ordered non-reflexive pair certificates passed a structural checker over the reported primitive rules. This is one family, and no new Lean verification is inferred from the Python replay. For a historical hypothesis-replacement review task, the packet compiler selected six source blocks covering five authored obligations in 4,494 UTF-8 bytes. No learner comparison was run.

### Proposed empirical boundary

> The central empirical question is whether the compiled record improves correctly interpreted, verified outcomes for a later consumer at equal total resources. A controlled comparison holds the target, model, accessible sources and cost policy fixed while varying presentation and route-history availability. It records the actual exposed packet, proof and interpretation judgments, consumer use and all construction and review costs.

The most important missing table is consequently a **consumer-intervention table**, with the actual exposed context, checked output, interpretation judgment, downstream use and total cost.

I would freeze broad restatement sweeps scored by changed-slot count and expansion of dormant orchestration without a concrete consumer. Move detailed inactive infrastructure to an appendix. Preserve the historical records and failures. Remove duplicated state ownership, not inconvenient evidence.

# 6. Wildcard: make stalled routes into standing typed queries

The record should also know **when an old route becomes worth revisiting**.

A stalled route can retain a precise next action and the typed inputs that would enable it. When a new admitted supply appears, the system checks whether all those inputs are now available under the current source policy.

That is a much more discriminating trigger than periodically rereading the entire archive or opening another general “continue this problem” task.

The returned `newly_enabled_routes` function operates on exact, already context-qualified interface identifiers. It emits a re-entry event only when every required input is available and at least one was previously missing.

A wake event means **the next step is enabled**, not that the target is solved. The upstream relation layer must establish the types and permitted context transports.

This complements negative-history reuse. A scoped obstruction prevents a precise repeated mistake. A newly supplied input revives a precise suspended action.

The first step is to annotate one genuinely available historical route’s next action and missing inputs. `WILDCARD.md` identifies A15 as a review candidate, explicitly requiring its historical source to be recovered before assigning formal meaning. No new domain theorem is required to implement the trigger.

# What Type A should do next

1. **Integrate the contextual record on a small source slice.** Run the 96 tests, replay the archived class with its correct stamp, and probe `ContrastKernel.lean`. Adapt the context-and-reverse-proof patch only after checking its base hashes. Include dependent-telescope controls and retain the existing closed-contract guard.

2. **Compile the next packet from immutable evidence groups.** Reproduce the 4,494-byte review packet, retain its audit manifest separately and open custody before delivery. Feed the selected source manifest into the existing handoff builder. Then test the same mechanism on a different reviewed family.

3. **Require every return to reach its consumers.** Extend the existing intake and coverage ledger with duplicate-safe custody and explicit dispositions, including the next packet where a correction changes future context. Process already-reviewed stranded work through its existing ownership and merge decisions.

4. **Produce complete dependency evidence before claiming strict withholding.** Retain transitive type and value dependencies and recompute formulation classes after masks. Keep unsupported interventions labelled unsupported.

5. **Run the matched-budget, family-level consumer experiment.** Compare with a strong manual packet; separate formulation choice from failed-history availability; measure actual use and full costs. Add one typed route-reactivation subscription as a second-generation test.

6. **Revise the systems paper from those results.** Use the supplied replacement passages now for the design and structural pilot. Add a claim of improved research performance only when the consumer experiment establishes it.

**The opportunity is to make every validated correction alter what the next reasoner receives, while using equivalence to reuse the correction without confusing reuse with discovery. That gives the restatements and failures a concrete role in improving the research process.**

