# Supplied snapshot excerpts

These excerpts record the attached packet, not the current state of a remote service or private checkout. The original path, whole-file digest and line range identify the supplied bytes. The excerpts are supporting source material; they are not execution receipts or independent reviews.


## private-reflection

Origin: `private snapshot:tools/meta/bridge/type_b_reflect.py`

Whole-source SHA256: `187d79a396dd232a09a9c379c4b290e1ac7d52d31bbd2036f553ea5b01aa42d9`

Source lines: 1-39

```text
#!/usr/bin/env python3
"""Reflection at any scope over the Type A / Type B loop: scaffold it, check it, admit what it learned.

One operator serves every granularity. A scope is one return, a batch, a packet kind, a problem, a policy, a date
window or the whole corpus, and scopes mix (union by default, --intersect for the overlap). The same reflection
can look at any layer (lens): outcomes, the policies we ask with, the mathematics, what the packet exposed, how we
assimilated, the infrastructure, and the objective itself. Anything can improve; how much a finding may change
depends on its layer:

* mathematics goes to its owners as tasks (abstract-and-apply, compositions, unmet needs);
* a policy (codex/standards/type_b_packet_rules.json, layer ``policy``) moves one status step per reflection,
  and only with evidence: candidate -> active needs a causal_trial_contract, evidence from two batches and a
  clean replay; any reflection may narrow or retire one;
* directives and the telos change only on the operator's word: reflections write proposals, never edits;
* invariants never change here.

Stores:
  state/formal_math/type_b_return_batches/<batch>/intake.json     custody, read only here (judgment-free)
  state/formal_math/type_b_reflections/outcomes/<batch>.json      one outcome row per return (written by admit)
  codex/standards/type_b_packet_rules.json                        the policy ledger (written by admit)
  codex/standards/plectis_objective_stack.json                    telos, objectives, proxies (read only here)
  state/formal_math/type_b_reflections/<id>/{REFLECTION.md,reflection.json}, index.jsonl

Commands:
  init   --id ID --scope S [--scope S ...] [--intersect] [--lens L,...] [--manifests DIR]
  check  DIR            exit 1 until every section, outcome row, verdict and delta is complete
  admit  DIR [--dry-run]
  due                   closed batches since the cutover with no reflection; exit 1 when one is due
  replay --rule ID [--manifests DIR ...]   would this rule, enforced, have blocked a packet whose return was
                        positive? A replay can veto a rule; it never justifies one.
  policies              the ledger at a glance
  use    --batch B --return R --by LOCATOR --what TEXT   record forward use of a result (objective O6)

Scopes: batch:<id>  return:<batch>/<return>  kind:<kind>  problem:<n>  policy:<rule>  since:<YYYY-MM-DD>  corpus
Lenses: outcomes, policy, mathematics, context, assimilation, infrastructure, objective (default: all)

The template with the questions per section is codex/standards/type_b_reflection_template.md.
"""
```


## private-writer

Origin: `private snapshot:tools/meta/dissemination/mathematician_outreach_typeb/build_short_paper_refinement_packets.py`

Whole-source SHA256: `dc578d402712f21ed6690e37e09d38af25c22c35a27fb0bad73563f26f74c638`

Source lines: 1-32

```text
#!/usr/bin/env python3
"""Nine source-frozen editorial packets; no proof-search or correspondence assignment.

Reuses the dissemination packet ZIP writer. Each new round snapshots the accepted
manuscripts afresh. The return checker checks transport and accounting, not truth.
"""
from __future__ import annotations

import argparse
from collections import Counter
import datetime as dt
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import unicodedata
import zipfile

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT))
from tools.meta.dissemination.mathematician_outreach_typeb import build_significance_packets as sig
from tools.meta.dissemination.erdos_exposition_critique.theorem_inventory import RESULT_ENVS

SCHEMA = "short_paper_refinement_v1"
SYSTEM = "claim-faithful-publication-systems"
COMPANIONS = ("cold-clone-to-proof-receipt", "open-source-mathematics-strategy")
PROBLEMS = ("68", "243", "249", "251", "257", "269", "1041", "1049", "systems")
BIB = re.compile(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}(.*?)(?=\\bibitem|\\end\{thebibliography\})", re.S)
RESULT = re.compile(r"\\begin\{(" + "|".join((*RESULT_ENVS, "conjecture")) + r")\}(.*?)\\end\{\1\}", re.S)
LABEL = re.compile(r"\\label\{([^}]+)\}")
```


## private-writing-brief

Origin: `private snapshot:tools/meta/dissemination/mathematician_outreach_typeb/build_short_paper_refinement_packets.py`

Whole-source SHA256: `dc578d402712f21ed6690e37e09d38af25c22c35a27fb0bad73563f26f74c638`

Source lines: 125-175

```text
This is an editorial assignment. Read the complete short paper and long record
before choosing a new order. Reconstruct their existing arguments and read the
relevant included originals. The deliverable is a substantially better complete
short manuscript, not suggestions, a referee report alone, or new mathematics.

## What to achieve

Choose the strongest substantial **established** contribution that earns the
reader's attention. Explain how it differs from antecedents and where the hard
idea lies. Lead with that contribution; keep routine consequences subordinate.
Do not confuse formalisation effort, a large proof, or an impressive label with
mathematical significance. You may judge a result routine or inherited. Preserve
credit and the scope of every conditional result and unresolved conjecture.

Read `skills/formal-math-exposition/SKILL.md` and all three references. The writing
mechanics attribute Tao, Gowers, Cohn, Conrad, Reiter, Pak and Milne, with their
provenance limits. Apply the first-time-reader contract prompted by van Doorn:
ordinary mathematical names, useful notation, understandable restrictions, and
standard tools described as standard tools. Read the Tao reading/writing gate.
Use the included original papers to learn disciplinary conventions, proof pacing
and economical exposition; do not copy passages or imitate a named author's voice.
The AI essays are background about understanding and attribution, not compulsory
material for an introduction. Check the citation index before claiming to have read
a source. An excerpt or metadata record is not a full paper.

Build one narrative: problem and motivation, exact contribution, revealing example,
proof idea, necessary definitions, hard step, argument, and honest boundary. Choose
the order that serves this paper rather than enforcing those as section headings.
Prefer natural declarative prose. Remove repeated qualification, internal workflow
names, proof-status clutter and empty promotion. Keep a compact truthful verification
note and stable links. Do not hide limitations in pursuit of smoother prose.

Keep the short paper as short as the mathematics warrants; no arbitrary page quota.
You may move secondary results, extended computations and elaborated ordinary proofs
to the long record. Retain enough of the central argument for a mathematician to
understand the mechanism and assess the hard step without Lean or an AI assistant.
Link precisely to the complete proof. Never replace an essential argument by “Lean
proves it”. Do not shrink typography to fit. The long record is supporting storage,
not a second whole-paper rewrite assignment. Update it only where the short revision
requires a move, cross-reference, or consistency repair.

## Frozen mathematical scope

Do not strengthen theorems, weaken hypotheses, introduce unproved claims, solve the
original open problem, or embark on new proof search. Do not modify Lean. If an
existing proof looks wrong, identify the exact passage in BLOCKERS.md, preserve the
issue, and give a safe editorial recommendation; never silently fix it by assuming
a stronger fact. Discovery of a proof problem does not turn this job into a research
packet. Lean sources and evidence are read-only references, not a fresh build receipt.
Preserve distinctions among paper proof, exact Lean theorem, checking evidence,
third-party mathematical review, and mere assertion. No checker status is improved
```


## private-custody

Origin: `private snapshot:tools/meta/bridge/type_b_return_intake.py`

Whole-source SHA256: `245fa1681d0a04e6da2e75c97830061beb3a02549137815dce32ce937fc9ed7f`

Source lines: 1-70

```text
#!/usr/bin/env python3
"""Byte custody for a Type B return batch. Custody only: no judgment, ever.

WHAT THIS IS FOR
----------------
``type_b_batch_math_assimilation`` requires a compaction-safe intake capsule before
deep reasoning starts, and specifies it exactly::

    state/formal_math/type_b_return_batches/<batch_id>/
      intake.json          append-only by arrival
      sources/<return_id>.<original-extension>

with each row recording the original path or message identity, byte length,
SHA-256, media type, capture time, packet/run identity when known, and the
preserved source path. It further requires that after every compaction, restart or
handoff you "re-open intake.json, verify the arrived source count and digests, then
resume from the coverage ledger".

Twelve batches exist on disk. Nothing writes them; every capsule is hand-authored,
and the verify step is hand-done across up to seven returns. This module does that
mechanical half against the schema those capsules already use,
``type_b_return_batch_intake_v0``. It introduces no second schema.

WHAT THIS IS NOT
----------------
It performs **no** claim extraction, no normalisation, no cross-return matching, no
disposition, no coverage ledger and no consensus of any kind. That work is
mathematical judgment and the skill owns it, explicitly requiring comparison that is
"semantic and mathematical, not merely identifier or sentence similarity" and naming
majority voting across returns as an anti-pattern. ``claim_ids`` is written as an
empty list for the skill to fill.

A prior tool in this repository tried to automate the judgment half with lexical
similarity and consensus counting. It was deleted before it landed. Do not rebuild
it here.

PRESERVATION MODE
-----------------
``copy`` is the default and the safe one: bytes land in ``sources/`` under repository
custody. ``reference`` records a digest against a path this module does not own, and
the existing capsules use it against ``~/.codex/attachments/...``, which is exactly
the volatile location the skill says to promote out of. ``verify`` is what makes that
risk visible rather than silent.

USAGE
-----
    type_b_return_intake.py open   --batch-id <id> --campaign "<identity>" \
        --evidence-boundary "<what these bytes are and are not>"
    type_b_return_intake.py add    --batch-id <id> --return-id <rid> --source <path> \
        [--provenance "..."] [--packet-identity "..."] [--reference]
    type_b_return_intake.py add-from-transcript --batch-id <id> --contains "<unique phrase>" \
        [--session-id <claude session>] [--transcript <path>] [--split-regex '<re>'] \
        [--strip-wrapping-braces] [--return-id-prefix r] [--return-ids a,b,c]
    type_b_return_intake.py verify --batch-id <id>
    type_b_return_intake.py verify-all

CLAUDE CODE: NEVER RETYPE A PASTED RETURN
-----------------------------------------
When the operator pastes returns into a Claude Code chat, the bytes are ALREADY on
disk in the session transcript (``~/.claude/projects/<cwd-slug>/<session>.jsonl``).
Re-emitting them through ``Write`` or a heredoc burns the whole output budget on a
copy the machine can make for free, and a hand copy is not byte custody anyway.
``add-from-transcript`` locates the user message, optionally splits it into one file
per return, and records each with the transcript as ``original_path``. The runtime
hook denies direct ``Write`` into a capsule ``sources/`` directory for this reason.
    type_b_return_intake.py close  --batch-id <id>
    type_b_return_intake.py reopen --batch-id <id> --reason "<why>"
"""
from __future__ import annotations
```


## round10-contract

Origin: `packet contract:SYSTEM_CONTRACT.md`

Whole-source SHA256: `fd1f9d2012dc47c044312ace769d421cfabc1d7dfa8b1acf7dbf705aec65376f`

Source lines: 1-63

```text
# Round 10: one system, seven parts, one paper

Seven Type B sessions run in parallel, one per part of the Plectis system. Each session upgrades its part in code,
writes that part's section of the systems paper from what the code now does, and places the part against its
literature. The sessions cannot see each other; this file is how their returns fit together.

## What the system is for

Plectis turns hard problems into mathematics that other mathematicians can understand, check and reuse, and it
records how it did so. Its visible outputs are papers: for each of eight Erdős problems (68, 243, 249, 251, 257, 269,
1041, 1049) a short paper that builds theory (the general statement first, the mechanism, the hard step, the problem
as an instance, evidence at each claim) and a long reasoning record; and a systems paper describing the machinery.
The operator's decision on 29 September 2026: rounds now improve the system and its papers. New mathematics mining is
paused; the corpus, Lean and Comparator evidence already hold far more than the papers present well.

## The pipeline and who owns which part this round

| Packet | Part | Consumes | Produces for the others |
|---|---|---|---|
| p1 | Pre-digestion: corpus to a per-problem dossier | research record, claims, relations, Lean index | `dossier/1` JSON per problem (schema below) |
| p2 | Verification to claims: Lean and Comparator evidence on every paper claim | claims, Comparator receipts, Lean declarations | `claim_evidence/1` rows per paper claim |
| p3 | The short-paper writer: dossier to short paper | `dossier/1`, `claim_evidence/1`, writing standard | a short-paper contract, linter and draft generator |
| p4 | Long reasoning records: assembly and navigation | reasoning parts, dossier | assembled long records consistent with the short papers |
| p5 | The self-improving loop: packets, custody, reflection, policy | round histories, ledger | loop upgrades; the round history as data |
| p6 | Evaluation with Type B sessions as subjects | every packet the system sends | rubric, grader packets, score ledger, round-11 design |
| p7 | The systems paper as a whole | all of the above | the revised paper; the section map others write into |

## Interfaces (version 1; propose changes as a versioned amendment in your return, never a silent fork)

`dossier/1` (one per problem; p1 owns, p3 and p4 consume):
`{problem, results: [{id, statement, generality, mechanism_sentence, hard_step, evidence: {class: lean|comparator|ordinary_reviewed|computed|cited, locators: []}, consumers: [], attribution, open_questions: []}], landscape: {routes: [], failed_routes_with_scope: [], generalisations: []}, sources: []}`

`claim_evidence/1` (p2 owns): `{paper_id, claim_locator, statement_hash, evidence_class, lean_declaration, comparator_receipt, ordinary_proof_locator, status_phrase_required}`

`rubric/1` (p6 owns; every writing packet's output is scored against it, blind to which variant produced it):
items with a 0 to 2 anchor each, for example generality stated, mechanism stated, hard step named, problem as
instance, evidence at the claim, register rules, faithfulness to the dossier, a cold reader's answers to checkable
questions.

`section/1` (p7 owns): each of p1 to p6 returns its systems-paper section as LaTeX in the paper's style, every
sentence about the system bound to a path, command or receipt, every number produced by a named builder.

## Rules that hold for every packet

- No paid model calls, API keys or hosted evaluations. The subjects of evaluation are the Type B sessions the system
  already sends: give packets different inputs, grade their returns blind with a fixed rubric, compare.
- Upgrade the native owner files (public `plectis-erdos` scripts and papers, private `ai_workflow` tools in
  `plectis_private_system.zip`). Return patches or full files with tests that run offline.
- Literature: your packet names its literature in `LITERATURE.md`. Read the primary texts you rely on (annexes are in
  `plectis_annexes_all.zip` and `plectis_annexes_fulltext.zip`). State exactly what the strongest existing system does
  and where your part goes further, with the evidence. Where it does not go further, say so.
- Evidence classes stay honest: Lean-checked, Comparator-checked, reviewed ordinary proof, computed, cited. Round 9's
  reflection found that every return corrected at least one overstated statement in the packet floor; check what you
  are told before you build on it.
- House register for any paper text: no em dashes, no "not X but Y" constructions, no novelty or priority claims, no
  claims of review or verification that did not happen.

## What comes after this round

Round 11 is nine paper packets, one per problem (short paper with its long record) and one for the systems paper,
built from the upgraded pipeline and scored with `rubric/1`. Where a pipeline change is in question, two packets get
the same assignment with one input changed, and the blind scores are the measurement. Rounds repeat until the papers
stop improving on the rubric.
```


## round10-state

Origin: `packet state report:02_CURRENT_STATE.md`

Whole-source SHA256: `8ee02c5bf9a19cb35ab038e45fc050f2fc646ec354b824e4f12efa02469f5731`

Source lines: 1-29

```text
# Current state (29 September 2026)

**Source.** `plectis_source.zip` is the complete tracked source of `plectis-erdos` at
`5acddfb2d9b43ad1b876f25700c49b1c39beddde` (the round-8 integration branch; public `main` is `c335dc2c`). It holds
the Lean library, the papers (TeX under `paper/`, rendered text under `docs/papers/full-text/`, registry
`docs/papers/corpus.json`), the research record (`docs/research-commons/record/`), claims (`docs/claims.json`),
Comparator evidence (`evidence/comparator/`, `verification/`) and the native Python runtime (`scripts/`).

**Private machinery.** `plectis_private_system.zip` holds the committed private tools this round upgrades: the Type
A/Type B packet builder, lint, custody and reflection engine with their tests, the policy ledger and objective stack,
the nine-paper refinement builder, the writing skills (`formal-math-exposition`, `humanizer`, the mathematical
reasoning gate), reading notes on self-improving systems and on the AI essays, the essay bundle, the two admitted
reflections, and the earlier Type B returns on the systems paper.

**Papers.** 22 registry entries: for each problem a short paper and a long reasoning record (for #249 and #257 also a
joint main paper), a joint reading note, and the systems papers: *Problem-Sized Lean Worlds*
(`paper/systems/claim-faithful-publication-systems-paper.tex`), *From a Cold Clone to a Proof Receipt*, *From Spare
Compute to Cumulative Mathematics*, *Plectis: What a Stranger Can Check*. A nine-paper editorial round was built on
28 September (`build_short_paper_refinement_packets.py`) and never sent; round 11 will supersede it.

**What rounds 8 and 9 showed.** Round 9 (`round9_review_and_reflection.zip`): five mathematics returns, each a
positive general result or a counterexample to a belief, none reviewed yet; the three "solve" asks decided nothing;
every return corrected at least one statement in the packet floor (pre-solve overclaims, a misread literature
functional, a baseline that counted future dependency edges). Two round-9 infrastructure returns built an evaluation
gym and a hill-climbing engine; nothing has run on a real model, and the operator has ruled out paid model calls.
The evaluation now uses Type B sessions as subjects (see `SYSTEM_CONTRACT.md`).

**What ran for this packet.** Nothing new was compiled or executed when this packet was built. Round 9's return
tests ran on Type A's machine (reported in the reflection). No Lean build, no paper build, no model run.
```


## lit-alphaevolve

Origin: `attached primary text:arxiv-2506-13131-v1/extracted.md`

Whole-source SHA256: `47c57adbe3d6f5312e2ac9299b8404cad21c352f989bbf780976dc876e0364b6`

Source lines: 86-371

```text
### Task specification

\labelsubsec:specification

##### Evaluation.
Since AlphaEvolve tackles problems with machine-gradeable solutions, the user must provide a mechanism for automatically assessing generated solutions.
This mechanism takes the form of a function $h$ mapping a solution to a set of scalar evaluation metrics.
By convention, these metrics are maximized.
In our current setup, $h$ is typically implemented as a Python function, called evaluate, with a fixed input/output signature, returning a dictionary of scalars.

Depending on the application, executing this function may take only seconds on a single device or spawn extensive computations. For mathematical problems, the function $h$ is typically very simple.
For example, when wishing to find largest possible graphs satisfying a given property, $h$ invokes the evolved code to generate a graph, checks whether the property holds, and then simply returns the size of the graph as the score.
In more complicated cases, the function $h$ might involve performing an evolved search algorithm, or training and evaluating a machine learning model.

##### API.
To support evolving multiple components across a codebase, AlphaEvolve exposes an input API where blocks of code can be annotated as to-be-evolved-by-the-system; see Figure~fig:grounding-api for an illustration. This design facilitates integrating it with existing codebases while requiring only minimal changes, simply by adding special markers (# EVOLVE-BLOCK-START and # EVOLVE-BLOCK-END) as comments into the code.

Any user-provided code inside such evolution blocks serves as the initial solution to be improved by AlphaEvolve, and the rest of the code forms a skeleton that ties the evolved pieces together, so that they can be invoked from evaluate.
While this initial implementation must be complete, it can be rudimentary---for instance, consisting of single-line functions that return constants of the appropriate types.

[htbp]

[c]0.48\textwidth

[t]\textwidth

[fontsize=, bgcolor=backcolour]python
# EVOLVE-BLOCK START
"""Image classification experiment in jaxline."""

import jax
...
# EVOLVE-BLOCK-END

...

# EVOLVE-BLOCK-START
class ConvNet(hk.Module):
def __init__(self, num_classes): ...
def __call__(self, inputs, is_training): ...

def sweep():
return hyper.zipit([...])
# EVOLVE-BLOCK-END

...

def evaluate(eval_inputs) -> dict[str, float]:
...
return metrics

\captionsetupjustification=centering, singlelinecheck=false
\caption\raisebox-0.3\baselineskip\includegraphics[height=1.8em]assets/human-icon.png
\labelfig:grounding-api

[b]\textwidth

[fontsize=, bgcolor=backcolour, escapeinside=||, breaksymbolleft=]python
|The current model uses a simple ResNet architecture with only three ResNet blocks. We can improve its performance by increasing the model capacity and adding regularization. This will allow the model to learn more complex features and generalize better to unseen data. We also add weight decay to the optimizer to further regularize the model and prevent overfitting. AdamW is generally a better choice than Adam, especially with weight decay.|

<<<<<<< SEARCH
self._block1 = ResNetBlock(num_channels)
self._block2 = ResNetBlock(num_channels * 2, stride=2)
self._block3 = ResNetBlock(num_channels * 4, stride=2)
=======
self._block1 = ResNetBlock(num_channels)
self._block2 = ResNetBlock(num_channels, stride=1)
self._block3 = ResNetBlock(num_channels * 2, stride=2)
self._block4 = ResNetBlock(num_channels * 2, stride=1)
self._block5 = ResNetBlock(num_channels * 4, stride=2)
self._block6 = ResNetBlock(num_channels * 4, stride=1)
>>>>>>> REPLACE
<<<<<<< SEARCH
def optimizer(self, learning_rate):
return optax.adam(learning_rate)
=======
def optimizer(self, learning_rate):
return optax.adamw(learning_rate, weight_decay=1e-4)
>>>>>>> REPLACE

\addtocountersubfigure+1
\captionsetupjustification=centering, singlelinecheck=false
\caption\raisebox-0.5\baselineskip\includegraphics[height=2.0em]assets/llm-icon.png
\labelfig:grounding-llm

[c]0.48\textwidth

\textwidth

[fontsize=, bgcolor=backcolour, escapeinside=||, breaksymbolleft=]python
|Act as an expert software developer. Your task is to iteratively improve the provided codebase. [...]

- Prior programs

Previously we found that the following programs performed well on the task at hand:|

top_1_acc: 0.796; neg_eval_log_loss: 0.230; average_score: 0.513

"""Image classification experiment in jaxline."""
[...]
class ConvNet(hk.Module):
"""Network."""

def __init__(self, num_channels=32, num_output_classess=10):
super().__init__()
self._conv1 = hk.Conv2D(num_channels, kernel_shape=3)
self._conv2 = hk.Conv2D(num_channels * 2, kernel_shape=3)
self._conv3 = hk.Conv2D(num_channels * 4, kernel_shape=3)
self._logits_module = hk.Linear(num_output_classes)
[...]

|- Current program

Here is the current program we are trying to improve (you will need to propose a modification to it below).|

top_1_acc: 0.862; neg_eval_log_loss: 0.387; average_score: 0.624

"""Image classification experiment in jaxline."""
[...]
class ConvNet(hk.Module):
"""Network."""

def __init__(self, num_channels=32, num_output_classes=10):
super().__init__()
self._conv1 = hk.Conv2D(num_channels, kernel_shape=3)
self._block1 = ResNetBlock(num_channels)
self._block2 = ResNetBlock(num_channels * 2, stride=2)
self._block3 = ResNetBlock(num_channels * 4, stride=2)
self._logits_module = hk.Linear(num_output_classes)
|[...]

SEARCH/REPLACE block rules:
[...]

Make sure that the changes you propose are consistent with each other. For example, if you refer to a new config variable somewhere, you should also propose a change to add that variable.

Example:
[...]

Task
Suggest a new idea to improve the code that is inspired by your expert knowledge of optimization and machine learning.

Describe each change with a SEARCH/REPLACE block.|

\addtocountersubfigure-2
\captionsetupjustification=centering, singlelinecheck=false
\caption\raisebox-0.5\baselineskip\includegraphics[height=2.0em]assets/prompt-icon.png
\labelfig:grounding-prompt

\captionIllustrative example of applying AlphaEvolve to evolving a supervised learning pipeline. All snippets are abbreviated, with ellipsis (...) indicating skipped lines. (a) The user-provided file with blocks marked for evolution, and the special evaluate function that can be invoked to score the current version of the code. (b) Example of an assembled prompt to be provided to the LLMs. (c) Example output generated by the LLM. The proposed diffs in (c) will be applied to the "current program" shown in the prompt (b), and the resulting modified program will then be sent to the evaluators. The evaluators will invoke the evaluate function from (a) in order to obtain the scores of the newly proposed program.
\labelfig:grounding

##### Flexibility in choosing the abstraction.
AlphaEvolve can be applied to the same problem in very different ways---especially when the evolved programs are not the final output but a means to discover solutions.
For example, AlphaEvolve can evolve the solution in raw string representation (as in classical evolutionary algorithms); evolve a function of a definite form that specifies how to construct the solution from scratch (the approach taken in~[citation: paredes2023mathematical]); evolve a bespoke search algorithm to find the solution within some fixed compute budget; or even co-evolve intermediate solutions and search algorithms together, such that each search algorithm is specifically tailored to further improve upon a particular intermediate solution.

We find that different levels of abstraction work better for different problems.
For example, we hypothesize that for problems with highly symmetric solutions it is advantageous to evolve constructor functions as these tend to be more concise~[citation: paredes2023mathematical], whereas for problems with non-symmetric solutions it works better to evolve customized search algorithms.

### Prompt sampling

\labelsubsec:prompting

As AlphaEvolve leverages SOTA LLMs, it supports various types of customization and providing long contexts as part of the primary evolution prompt.
This prompt comprises multiple previously discovered solutions sampled from the program database, as well as system instructions on how to propose changes to a particular solution.
Beyond these key ingredients, users can further tailor prompts to their specific needs in different ways, such as the following.

-
Explicit context: details about the problem being solved, such as fixed human-written instructions, equations, code snippets, or relevant literature (e.g., pdf files).

-
Stochastic formatting: template placeholders with human-provided alternatives for increased diversity, instantiated using probability distributions provided in a separate config file.

-
Rendered evaluation results: usually this will include a program, the result of executing that program, and the scores assigned by the evaluate function.

-
Meta prompt evolution: instructions and context suggested by the LLM itself in an additional prompt-generation step, co-evolved in a separate database analogous to the solution programs.

### Creative generation

\labelsubsec:generation

To drive the evolutionary procedure, AlphaEvolve leverages the capabilities of SOTA LLMs, whose principal role is to digest information about previously developed solutions and propose new, diverse ways to improve the solutions.
Although AlphaEvolve is model-agnostic, in ablations we observe that AlphaEvolve performs increasingly better as the underlying LLM improves (see~sec:ablations_rewrite).

##### Output format.

When AlphaEvolve asks an LLM to modify existing code, especially within larger codebases, it requests the changes to be provided as a sequence of diff blocks in a specific format:

<<<<<<< SEARCH
# Original code block to be found and replaced
=======
# New code block to replace the original
>>>>>>> REPLACE

Here, the code between \texttt<<<<<<< SEARCH and ======= is the exact segment to match in the current program version. The code between ======= and \texttt>>>>>>> REPLACE is the new segment that will replace the original one.
This allows for targeted updates to specific parts of the code.

In cases where the code being evolved is very short, or when a complete rewrite is more appropriate than a small modification, AlphaEvolve can be configured to instruct the LLM to output the entire code block directly, rather than using the diff format.

##### Models used.

AlphaEvolve employs an ensemble of large language models. Specifically, we utilize a combination of Gemini 2.0 Flash and Gemini 2.0 Pro.
This ensemble approach allows us to balance computational throughput with the quality of generated solutions.
Gemini 2.0 Flash, with its lower latency, enables a higher rate of candidate generation, increasing the number of ideas explored per unit of time.
Concurrently, Gemini 2.0 Pro, possessing greater capabilities, provides occasional, higher-quality suggestions that can significantly advance the evolutionary search and potentially lead to breakthroughs.
This strategic mix optimizes the overall discovery process by maximizing the volume of evaluated ideas while retaining the potential for substantial improvements driven by the more powerful model.

### Evaluation

\labelsubsec:evaluation

To track AlphaEvolve's progress and to select which ideas to propagate in future generations, each new solution proposed by the LLMs is automatically evaluated.
In principle, this process amounts to simply executing the user-provided evaluation function $h$ on the generated solution.
In practice, AlphaEvolve supports optional mechanisms to make this evaluation more flexible and more efficient:

-
Evaluation cascade (hypothesis testing): the user can specify ensembles of test cases of increasing difficulty, such that new solutions are  evaluated on the next stage only if they achieve sufficiently promising results in all earlier stages.
This helps to prune out less promising solutions more quickly. Moreover, new solutions are initially evaluated on a small scale before being subjected to the main test cases, to filter out faulty programs early.

-
LLM-generated feedback: in some applications, desirable solutions have certain characteristics that are difficult to capture precisely in the user-provided evaluation function $h$; for example, simplicity of the discovered program.
These properties can be graded using separate LLM calls and added to the dictionary of scores to steer evolution, or they can be used to discard solutions when a criterion is not fulfilled.

-
Parallelized evaluation: the sample efficiency of AlphaEvolve makes it feasible to spend on the order of 100 compute-hours to evaluate any new solution.
However, unless individual evaluations are parallelized to reduce their wall-clock duration, this can slow down the rate at which new generations appear, limiting the ability of the evolutionary algorithm to apply several consecutive mutations.
In many applications, evaluation is embarrassingly parallel (for example, running a search algorithm from multiple randomized initializations), allowing AlphaEvolve to distribute this work through asynchronous calls to an evaluation cluster.

##### Multiple scores.

AlphaEvolve allows for optimizing multiple user-provided scores, i.e., evolving objects that achieve a high score under one or multiple evaluation metrics.
This has both an intrinsic and instrumental value. While in multiple applications we genuinely care about developing solutions for multiple evaluation metrics (or one solution that is strong on all of them simultaneously), we find that even if one metric is of particular interest, optimizing for multiple metrics often improves results for the single target metric.
Perhaps this occurs because programs excelling under different evaluation criteria often possess distinct structures or logic and, by incorporating examples of these diverse, high-performing programs---each representing a different definition of ``good''---into the prompts provided to the language model, we can stimulate the generation of more varied candidate solutions, increasing the chances of discovering novel approaches that are highly effective for the target metric.

### Evolution

\labelsubsec:evolution

During its evolutionary procedure, AlphaEvolve continually generates a growing number of solutions with evaluation results (scores and program outputs) attached to them.
These solutions are stored in an evolutionary database, the primary goal of which is to optimally resurface previously explored ideas in future generations.
A key challenge in designing such databases is balancing exploration and exploitation, to continuously improve the best programs while maintaining diversity to encourage exploration of the entire search space.
In AlphaEvolve, the evolutionary database implements an algorithm that is inspired by a combination of the MAP elites algorithm~[citation: mouret2015illuminating] and island-based population models~[citation: tanese1989distributed, paredes2023mathematical].

### Distributed pipeline

\labelsubsec:pipeline

AlphaEvolve is implemented as an asynchronous computational pipeline (using the asyncio Python library) in which many computations are run concurrently, with each computation blocking (waiting) whenever its next step relies on the result of another, yet unfinished computation.
More specifically, the asynchronous pipeline comprises a controller, LLM samplers, and evaluation nodes.
The entire pipeline is optimized for throughput (rather than the speed of any one particular computation), in order to maximize the number of ideas that can be proposed and evaluated within a specific overall computation budget.

## Results

\labelsec:results

### Faster matrix multiplication via finding novel algorithms for tensor decomposition

\labelsubsec:matmul

[t]
\rowcolors2whitelightgray

ccc
$ m, n, p \rangle$ & best known [reference] & AlphaEvolve

$ 2, 4, 5 \rangle$ & 33 [citation: hopcroft] & 32
$ 2, 4, 7 \rangle$ & 46 [citation: smirnov2013bilinear] & 45
$ 2, 4, 8 \rangle$ & 52 [citation: smirnov2013bilinear] & 51
$ 2, 5, 6 \rangle$ & 48 [citation: smirnov2013bilinear]   & 47
$ 3, 3, 3 \rangle$ & 23 [citation: laderman]   & 23
$ 3, 4, 6 \rangle$ & 56 [citation: Kauers_2025]   & 54
$ 3, 4, 7 \rangle$ & 66 [citation: smirnov2021]   & 63
$ 3, 4, 8 \rangle$ & 75 [citation: smirnov2021]   & 74
$ 3, 5, 6 \rangle$ & 70 [citation: Kauers_2025]   & 68
$ 3, 5, 7 \rangle$ & 82 [citation: smirnov2021]   & 80
$ 4, 4, 4 \rangle$ & 49 [citation: strassen1969gaussian]   & 48
$ 4, 4, 5 \rangle$ & 62 [citation: kauers2023flip]   & 61
$ 4, 4, 7 \rangle$ & 87 [citation: smirnov2013bilinear] & 85
$ 4, 4, 8 \rangle$ & 98~[citation: strassen1969gaussian] & 96
$ 4, 5, 6 \rangle$ & 93 [citation: Kauers_2025]   & 90
$ 5, 5, 5 \rangle$ & 93 [citation: flip_graphs_with_symmetry]  & 93
\caption
Upper bounds on the rank of the tensor $ m,n,p \rangle$ representing the product of an $m n$ matrix and an $n p$ matrix, i.e.~the number of scalar multiplications required to compute this matrix product.
Beyond the examples shown here, for all parameters $m,n,p 5$, AlphaEvolve either matched or surpassed the best known solutions, and provided exact algorithms (see tab:relaxed-opt-results-appendix in appendix for full results).
```


## lit-etp

Origin: `attached primary text:arxiv-2512-07087-v2/extracted.md`

Whole-source SHA256: `eced4a47439551a342aa58f07c8577b323494ab2affe11347c82cdb59d793843`

Source lines: 327-382

```text
### The Blueprint tool

The formalization of proofs is an act of careful engineering. It is therefore helpful to have a blueprint with detailed natural language lemmata, definitions, and proof sketches in Lean. In the Lean community it has been conventional to use the Lean blueprint tool by Patrick Massot et al.~[citation: leanblueprint]. The typical formalization project has a clearly defined set of target theorems, and the authors of the project work with a known proof, to produce a clear roadmap for the formalization. The Lean blueprint tool is capable of linking each piece of this natural language document to its Lean encoding, tracking the dependency of definitions and theorems, and progress through them, by producing a key coloured dependency graph. Thus the managers of the formalization project can not only organise the project to distribute tasks among contributors, but also track when various pieces of the formalization are complete.

In this project, we were entering uncharted mathematical territory. We had a clear list of tasks to accomplish, namely to prove the implication or anti-implication between every pair of equational laws, up to transitivity and duality. At the same time there was no clearly known pen and paper proof available for any of these beforehand. This meant that we could not prepare the blueprint of the project in advance and organise the formalization around it. Thus the traditional roles played by the blueprint were replaced by a number of other tools and mechanisms. In particular, the dependency graph did not play its traditional role in formalization projects. We developed a number of visual tools to track our progress in the project in terms of remaining open implications and anti-implications (see sec:gui-sec). Within Lean, every equational result was tagged with the @[equational_result] attribute to identify the theorem as one of the project goals, and this attribute was used to collect the status of all the goal theorems of the project. Instead of covering the dependency graph node by node, progress in the project happened as various contributors uncovered some structural ideas or heuristics that helped ATPs solve one or more pairs of laws.

The blueprint tool played a very important role in recording our progress and formalizing these classes of implications or anti-implications. It is the only comprehensive record of all the techniques that were employed in the project. Further at the level of specific implications and anti-implications, the blueprint and formalization evolved as in other projects, hand in hand. As an example, the formalization of the anti-implication  $\Eq1729  \Eq817$ proceeded through several iterations of refinement of the blueprint and formalization.

In conclusion, when using ITPs for tackling open problems, especially at scale, we observed that the role of the blueprint changed, but it still remained an important way to track and document our progress at a local level across the project.

### The project template

When working on a formalization project, there are many moving pieces that need to work in concert. At the core level, there is the project set up by Lean's build and dependency management system lake. But in addition to that, there are several pieces, including the aforementioned blueprint tool, as well as scripts that a user may choose to run to visualise various aspects of the project, or check the project in specific ways, or compile documentation automatically as the project advances. These additional tasks are accomplished by a number of external tools, and combining them in a mutually compatible way can be challenging. We side-stepped most of these issues by using the GitHub template repository of Pietro Monticone~[citation: Monticone_LeanProject_2025]. At the same time, when we began the project, the template in place was suited for more conventional formalization projects and the tooling they required. It also did not include the scripts that enabled automated project management support that we added, as well as support for deploying our visualisation tools and the paper. Over the course of the project, the leanproject template in turn received substantial new additions. One elementary example is the addition of git pre-push hooks, which are scripts that perform a basic sanity check on the local working copy of a contributor before pushing their contributions to the central GitHub repository.

\subsectionThe Lean Zulip chat forum
The Lean community traditionally congregates on the leanprover Zulip chat forum\footnotehttps://leanprover.zulipchat.com. Our project was coordinated and organised primarily from this forum. At the beginning we created a channel called Equational. Zulip allows the creation and management of discussion topics within the scope of a channel. We made extensive use of the Zulip channel for several purposes. In the beginning it became the gathering point for new contributors. The new contributions process was designed and discussed on this forum. Later, topics were created for each specific technical topic, including the metatheory and its formalization, specific design decisions, specific implications and anti-implications, design of tools, etc. As shown in fig:proj_mgmt_flow, the Zulip chat served as the beginning of the contributions process for each piece of the project. Contributors first discussed their proposed contributions or specific problems they tackled on Zulip before following the steps of claiming tasks on GitHub, writing a blueprint write up and/or formalization.

### Organising the collaboration: the precedent set by the PFR project

When five people collaborate in person, splitting up the research on a question into subtasks and assigning them to collaborators can be accomplished by discussion and consensus. When there are more than fifty collaborators working together online, a more systematic approach is required. In previous formalization projects such as the formalization of the proof of the Polynomial Freiman--Ruzsa (PFR) conjecture [citation: PFR_Tao_Dilles_2023], tasks were managed over the Lean zulipchat forum. The organiser of the project, Terence Tao, posted a series of message threads. Each thread corresponded to a list of outstanding tasks. These tasks were then claimed by collaborators on Zulip. The claims were recorded on a first-come first-served basis by the organiser by tagging the respective users against the tasks. Contributors could claim any open task and disclaim tasks if they couldn't finish it, with the organiser keeping track of these requests. This system allowed contributors to take their time to flesh out their work, without worrying about competing claims to the same task. Further, it helped the organisers track the task assignment and communicate with the respective collaborators to track and ascertain progress. Unfortunately, this involved a lot of manual and time-consuming management of the task list by organisers. In this project, we automated several pieces of this approach. This freed up organisers to help contributors and review their contributions.

### Organizing the collaboration in this project

We adopted tools that are familiar to software engineers as ticket systems but are also known in the wider world of industrial production, such as the kanban system. Our project dashboard was built using the GitHub projects feature. We were able to encode some pieces of our automation using the standard GitHub-provided interface. For the rest, we relied on continuous integration scripts (hereon~CI). The exact flow of contributions is specified in the CONTRIBUTING.md file of the project repository~[citation: The_Equational_Theories_repository]. Briefly,

-  Tasks were proposed by organisers. A contributor might start a discussion on Zulip or raise an issue on GitHub to prompt the organisers to launch tasks.

-  Contributors could then claim tasks with a comment under the task. The CI ensured that at most one contributor could claim a task at any time.

-  Contributors could then work on the task and propose a corresponding pull request.

-  Upon completion of the task, the pull request received reviews, while the CI automatically checked that the project compiled and passed additional checks such as Lean's environment replay tool leanchecker and the semi-external checker lean4lean~[citation: lean4lean].

-  If all was well, the PR was merged onto the main branch of the project repository.

At any point in this process, the contributor could disclaim the task or replace a proposed PR with an alternative. In addition, organisers could always step in to fix any errors that occurred and follow up with contributors. Each of the steps described above happened automatically, triggered by a well-defined set of actions described in the CONTRIBUTING.md file. The typical workflow of this process is shown in the flowchart in fig:proj_mgmt_flow. The figure omits error handling and situations where organisers might manually intervene. The user interface to this project management is the GitHub project dashboard, of which we include a snapshot in fig:proj_dashboard

We note that our method has since been adopted by other major formalization projects including the one to formalize Fermat's Last Theorem [citation: FLT_Lean].

[t]

\includegraphics[width=.86,trim=70 110 240 70,clip]proj_mgmt_figures/task_flowchart.png
\caption\labelfig:proj_mgmt_flow A partial flowchart of the automated task management process. Each task corresponds to an issue. A pull request is created to resolve tasks and once a pull request linked to a task is merged, the task is considered complete. The thick boxes represent states of the project dashboard represented by task columns. The movement of tasks between these states is automated by the CI which is triggered upon specific actions performed by contributors on the respective GitHub issues and pull requests. A more detailed description is found in the contributions file of the GitHub file, named CONTRIBUTING.md by convention.

[t]

\includegraphics[width=1.0\textwidth]proj_mgmt_figures/proj_dash_snapshot.png
\caption\labelfig:proj_dashboard A snapshot of the project dashboard as of 30 July 2025

### Trusting ITPs to scale collaboration

In our project we used the interactive theorem prover (hereon ITP) Lean 4 [citation: the_lean4_paper] precisely to address these issues of scaling. The contents of this section are common knowledge in the ITP and ITP-adjacent research communities. The exposition is intended to be useful to a user of ITPs.

At its core, an interactive theorem prover implements an expressive logic, encoded in a suitable choice of mathematical foundations. Lean 4 has the calculus of constructions extended by inductive types as its core logic. This logic is sufficiently powerful to express mathematical definitions and theorems for almost all areas of mathematical interest, while being relatively spartan and easy to write proof checkers for. Additionally, modern ITPs provide a convenient programming language which helps express mathematical ideas in a syntax closer to a mathematician's intuition than would be permitted by raw logical terms. A subset of ITPs like Lean, Rocq (formerly Coq), and Isabelle go one step further and provide the means to generate proofs through so-called tactics. There are usually numerous tactics, each specialised for specific proof generation methods. Among other things, they search mathematical libraries, simplify expressions, and identify lemmas and hypotheses to make progress in proofs. The proofs generated by this overlying programming machinery are terms in the core logical calculus which are checked mechanically by the proof checker. But in a large project, there is more to trust. It helps to understand the nature and limits of trust one can place on ITPs.
\looseness=-1
```


## lit-architect

Origin: `attached primary text:arxiv-2601-22554-v1/extracted.md`

Whole-source SHA256: `4b874995c737d87d278988bfc0ae77e7eb139a280ca6d2c2ce573921320be94f`

Source lines: 45-105

```text
## Methods

### Overview

LeanArchitect is a tool for extracting blueprint information directly from Lean code. Its core design principle is to minimize duplication between \LaTeX and Lean, by treating Lean as the authoritative source of information for any formalized blueprint node.

The system introduces a new attribute, \leancode@[blueprint], which can be attached to Lean definitions and theorems. This attribute records metadata such as a \LaTeX label, natural language statements and proofs, and project-management annotations. In addition, LeanArchitect automatically infers metadata such as:

-  Dependencies between definitions and theorems,

-  Formalization status of the theorems (i.e., if they are \leancodesorry-free).

Blueprint data is stored in an environment extension and can be exported via a dedicated Lake facet. The exported artifacts consist of \LaTeX fragments, which integrate seamlessly with existing leanblueprint documents through macros such as \bplatexcode\inputleannode. See fig:leanarchitect-workflow for a diagram.

[ht]

\textwidth
\includegraphics[page=1,width=\textwidth]figs/LeanArchitect.drawio.pdf

Caption: Blueprint generation workflow without .

\textwidth
\includegraphics[page=2,width=\textwidth]figs/LeanArchitect.drawio.pdf

Caption: Blueprint generation workflow with .

\captionComparison of blueprint generation workflows with and without using LeanArchitect. (a) Without LeanArchitect, the entire \LaTeX blueprint needs to be manually written and synchronized with the evolving formalization part. (b) With LeanArchitect, maintainers only need to manually write the structure of the \LaTeX blueprint, whose dependency relations and formalization status are automatically synchronized from the corresponding Lean part.
\labelfig:leanarchitect-workflow

This design supports a workflow in which informal exposition and formal proofs evolve together, while minimizing manual duplication and enabling structured interaction with AI automation.

### Blueprint Attribute

LeanArchitect provides a new Lean attribute \leancode@[blueprint] that can be attached to definitions and theorems. Users can optionally supply metadata such as a \LaTeX label, natural language statement and proof, and other project-management annotations. The attribute serves as the user interface between Lean code and the blueprint system. A typical example is:

@[blueprint "thm:add-comm"
(statement := /-- Addition in $ℕ$ is commutative. -/)]
theorem §\declnameMyNat.add_comm§ (a b : MyNat) : a + b = b + a := by
/-- By induction and then lem:zero-add, lem:succ-add. -/
induction a with
| zero => exact b.zero_add
| succ a ih => sorry_using [MyNat.succ_add]

### Environment Extension

After tagging a declaration, LeanArchitect constructs an internal representation of the corresponding blueprint node and stores it in an environment extension \leancodeblueprintExt. For each tagged declaration, LeanArchitect automatically infers dependency information by recursively traversing the constants used in the type and value of the declaration, and determines proof status by checking if \leancodesorry is used. Then an internal \leancodeNode is constructed; e.g.~with the following data:

-- Identifiers
name := MyNat.add_comm, latexLabel := "thm:add-comm"
-- Statement status, dependencies, and text
statement :=  leanOk := true, uses := ["def:nat"],
text := "Addition in $ℕ$ is commutative."
-- Proof status, dependencies, and text
proof :=  leanOk := false, uses := ["lem:zero-add", "lem:succ-add"],
text := "By induction and then lem:zero-add, lem:succ-add."
-- Miscellaneous metadata
notReady := false, discussion := none, title := none

\subsection\LaTeX Export \labelsec:latex-export

To build the \LaTeX blueprint from such data, LeanArchitect provides a build-time export mechanism integrated with Lean's Lake build system, inspired by doc-gen4. For each module, blueprint data is extracted and rendered into \LaTeX fragments that can be imported into an existing blueprint document using the macro \bplatexcode|\inputleannodelabel|. Multiple Lean declarations are allowed to correspond to a single blueprint node. The export process is deterministic and incremental. For example, when the user writes \bplatexcode|\inputleannodethm:add-comm| in the \LaTeX blueprint, it will be expanded to:
```


## lit-interestingness

Origin: `attached primary text:arxiv-2609-28603-learning-to-discover-interesting-mathematics/extracted.md`

Whole-source SHA256: `dfc4556bc4617681de3bbb96ac323621373f240b983fb56ec18724a1a31c32e4`

Source lines: 76-100

```text
## The Intrinsic Interestingness of a Mathematical Statement {#sec:interestingness}

In this section, we attempt to define a notion of the interestingness of a mathematical statement or conjecture that aims to capture an *intrinsic* property of the mathematical result, ignoring any relation to the outside world, or to other parts of the mathematical literature. We claim that a statement $T$ is *interesting* given a set of premises $P$ if it is easy to state, and has a long and incompressible proof. To compute this, we can take a ratio between the length of a proof given some premises in terms of lines of code, and the number of characters of Lean 4 needed to state a theorem given some set of definitions one already has access to. For instance, one would expect that a theorem in probability theory is easy to state for a reader who already has a measure-theoretic vocabulary and enormously difficult for a reader given access to only statements in algebraic geometry. We recall the following quote by Pólya on the nature of aesthetics in math,

>  *"The elegance of a mathematical theorem is directly proportional to the number of independent ideas one can see in the theorem and inversely proportional to the effort it takes to see them."* -- *Mathematical Discovery,* [@polya1981mathematical]

Formally, for any Lean declaration $X$, let $S(X)$ denote the number of characters in its statement, and let $C(X)$ be the set of all definitions required to state $X$, including whatever definitions are needed to state those definitions, recursively. So $C(X)$ will contain all the definitions required to formally state $X$ from the axioms. We will then define the conditional description length as $$\begin{equation}
  L(T\mid P)\;=\;S(T)+\!\!\sum_{d\in C(T)\setminus C(P)}\!\!S(d).
  \label{eq:conditional-length}
\end{equation}$$

In this way, the term $L(T|P)$ counts the description length of all the definitions needed to state the theorem $T$, given access to all the definitions used in the premises $P$. We then formally define the conditional interestingness[^1] of a statement as $$\begin{equation}
  I(T\mid P)\;=\;100\;\frac{V(T\mid P)}{L(T\mid P)}.
  \label{eq:interestingness}
\end{equation}$$

We choose this definition to quantify the intrinsic difficulty of a mathematical statement as it is trivially possible to construct arbitrarily difficult statements, if we do not normalize by the description length of the statement. For instance, suppose we had a fixed set of premises $P$ and a set of theorems $\{T_1, T_2, \ldots\}$ that are all entirely unrelated and have a fixed proof length. Then the "theorem" $\hat T_n = T_1 \wedge T_2 \wedge \cdots \wedge T_n$ would have difficulty $V(\hat T_n | P) = O(n)$, whereas the interestingness is $I(\hat T_n | P) = O(1)$.

In the special case where we consider the empty set of premises, we can create an absolute scale of the interestingness of a mathematical statement $I_0(T) =I(T|\varnothing)$[^2]. With no premises, the denominator is the target's own vocabulary length, $L(T\mid\varnothing)=S(T)+\sum_{d\in C(T)}S(d)$. As we no longer require conditioning on a set of premises, the numerator can now be deterministically computed from a library such as [mathlib]{.smallcaps}, as we can just unroll the proof as written via premise expansion. The result (Figure [2](#fig:interestingness-model-free){reference-type="ref" reference="fig:interestingness-model-free"}) serves as a useful verification for the construction of our metric on existing statements of [mathlib]{.smallcaps}. We can see in the bottom decile simple algebraic relations, like for instance the identity that $1^n = 1$, and in the upper quartiles we see results such as special cases of Fermat's Last Theorem, which happen to require very little machinery to state but are tough to prove.

<figure id="fig:interestingness-model-free" data-latex-placement="t">
<embed src="figures/interestingness_model_free.pdf" />
<figcaption><strong>Quantifying the interestingness of a statement.</strong> Here we show the distribution of interestingness <span class="math inline"><em>I</em><sub>0</sub></span>, as defined in Section <a href="#sec:interestingness" data-reference-type="ref" data-reference="sec:interestingness">3.1</a>, of all statements from <span class="smallcaps">mathlib</span>. The resulting ordering is intuitive, with basic algebraic identities at the bottom, analysis in the middle because its definitional prerequisites are enormous, and theorems that are famously easy to state but hard to prove, like Fermat’s Last Theorem for exponent 3, at the top.</figcaption>
</figure>
```


## lit-openh

Origin: `attached primary text:arxiv-2607-09217/extracted.md`

Whole-source SHA256: `ccc908f3356ef2cdbcaa5a3d963f601f670cf1f61b9b74b3642e9b508ce28dc3`

Source lines: 54-80

```text
-12 5 **=** State and Memory Management

To preserve important context between Planner steps, OpenProver manages a single compact Markdown file called the *Whiteboard*, updated periodically by the Planner using the `write_whiteboard` action. While the content of the Whiteboard is decided solely by the Planner, it is advised by the corresponding prompt to contain at least the currently executed proof plan, the history of all already explored and failed attempts, and ideas to return to later, together with any useful brief observations and notes. The Whiteboard is provided to the Planner as input at each step. This design can be seen as analogous to the Reasoning Cache [@reasoning_cache], extending the effective context length of reasoning LLMs.

Additionally, the Planner occasionally needs to store longer text or Lean snippets such as detailed failed proof attempts, proofs of lemmas, literature summaries, and similar. To prevent overflowing the Whiteboard, OpenProver manages a *Repository* of items where each *Item* is either a Markdown file or a Lean file. Items are organized in a folder-like structure using the `write_items` and `read_items` actions, and are referred to by their relative path, which we call a *slug*. At each Planner step, alongside the Whiteboard, the Planner also observes the slugs and one-line summaries of all Items stored in the Repository. Crucially, Lean Items are only stored if they pass the Lean formal verification; otherwise, the errors and warnings are fed back to the Planner. This enables tighter feedback from the formal verifier than just a final-answer check.

-12 5 **=** Proof Search Loop []{#sec:proof_search_loop label="sec:proof_search_loop"}

OpenProver executes a linear proof search loop outlined in Algorithm [2](#alg:openprover){reference-type="ref" reference="alg:openprover"} until either a proof is found or the compute budget runs out. Parallelization is enabled by spawning multiple Workers.

<figure id="alg:openprover" data-latex-placement="t">
<div class="minipage">
<div class="algorithm">
<p>Initialize Whiteboard <span class="math inline"><em>W</em> ← ∅</span>, repo <span class="math inline"><em>R</em> ← ∅</span>, history <span class="math inline"><em>H</em> ← []</span> <em>(optionally, iterate <span class="nodecor"><span class="smallcaps">PlannerStep</span></span> further until <span class="nodecor"><span class="smallcaps">proof.lean</span></span> is produced)</em> write <span class="smallcaps">discussion.md</span> summarizing proof search process and result</p>
</div>
<div class="algorithm">
<p>Query planner LLM with <span class="math inline">(<em>W</em>, <em>R</em><sup>′</sup>, <em>H</em><sub>−<em>n</em>:</sub>, <em>T</em>)</span>: Produce reasoning trace (CoT) Produce free-form output and a list of actions <span class="math inline"><em>a</em><sub>1</sub>, …, <em>a</em><sub><em>k</em></sub></span> Run <span class="math inline"><em>a</em><sub>1</sub>, …, <em>a</em><sub><em>k</em></sub></span> in parallel and wait for completion Append each action’s output to <span class="math inline"><em>H</em></span></p>
</div>
</div>
<figcaption>High-level pseudocode of OpenProver: the main loop (Alg. 1) repeatedly invokes <span class="smallcaps">PlannerStep</span> (Alg. 2). </figcaption>
</figure>

-12 5 **=** Integration with Lean

OpenProver optionally integrates with the Lean formal verifier, with the only requirement that the formal theorem statement is provided on input in the form of a Lean file with one or more `sorry` keywords.

First, after a natural language proof is found, OpenProver attempts to formalize it and submit the resulting Lean proof. In case of errors or warnings emitted by the Lean verifier, OpenProver iteratively attempts to fix the proof, potentially transitioning back to fixing the natural language proof in case a flaw is identified.
```


## lit-agenthunt

Origin: `attached primary text:arxiv-2603-06737/extracted.md`

Whole-source SHA256: `2c2f3c10ceea8d912094ef926839a36e38dd8b90318980ce43007dbf834bcba0`

Source lines: 1-46

```text
# Motivation: Fast Parallelized LLM Autoformalization

LLM agents [@DBLP:conf/nips/SchickDDRLHZCS23; @DBLP:conf/iclr/YaoZYDSN023] have recently shown promising results in autoformalization of large portions of mathematical textbooks [@urban2026130klinesformaltopology]. While this is encouraging, the general topology project reported in [@urban2026130klinesformaltopology] was as of February 18, 2026, still ongoing.[^1] This means that two months after its major launch, it was not yet finished, even though is has reached over 350k lines.

In this work we therefore explore how multiple LLM agents can collaborate on such large projects, parallelize the work efficiently, and progress in such large projects much faster than a single agent. The main idea is to use a bounty-based setting introduced by Hales in the Flyspeck project [@hales2012dense; @hales2017formal] and then let agents compete and collaborate in proving the theorems and collecting the bounties. Our hope is that such decentralized market setting will be easier and more flexible, than trying to plan upfront, centrally and manually the detailed division of labor between many agents. This is because large-scale formalizations may have unpredictable aspects to them, such as, e.g., gaps in the proofs, forward references, etc.

# Target: Autoformalization of Algebraic Topology in Megalodon

Since we are interested in building on the autoformalization framework developed in [@urban2026130klinesformaltopology], we use a very similar setting, using the Megalodon higher-order set theory proof checker [@DBLP:conf/mkm/BrownP19]. Since that project has already autoformalized the main general topology definitions and theorems in Munkres (part I, about 250 pages), our natural target is part II (Chapter 9 to 14, Sections 51 to 85) of Munkres, i.e., the remaining about 200 pages of algebraic topology.

## Initial Autoformalization of Statements and Setting of Bounties

A major change from the one-agent setting of [@urban2026130klinesformaltopology] is that we want to set up the formal definitions and theorems (*statements* below) upfront and attach adequate bounties on them. This to some extent corresponds to Hales's "Flyspeck blueprint" setting and book, with one expert mathematician making this high-level formal sketch and price estimation. We are aware that this can lead to problems if some statements are autoformalized wrongly (which did happen in [@urban2026130klinesformaltopology]). While in [@urban2026130klinesformaltopology], the single agent can recover and correct the statements, here we decide to fix them, so that the agents cannot game the system and collect bounties easily. We therefore invest a lot of effort into double-checking the initial autoformalized statements (and are also ready to step in as admins if we see a major problem later).

In particular, we initially gave the 200 Latex pages (together with the background theory) to a single LLM agent (Claude Opus 4.6) with stringent rules summarized as follows:

- The background file already contains a lot of foundational material (set theory, topology, etc.) to be re-used, and only the new algebraic topology section is allowed to be edited.

- The task is to formalize every definition and theorem from algtop.tex, in order, but without proofs (everything admitted for now). However, definitions must be mathematically meaningful (no dummy or stub definitions) and repeatedly double-checked.

- The process must be extremely disciplined: no duplicates, no adding extra lemmas not in algtop.tex, no modifying earlier parts of the file, frequent compilation checks with megalodon, regular backups, and careful progress tracking.

- There are strong quality-control rules: definitions must be substantive, infrastructure must be built properly, previous work must never be lost, and each theorem must include an effort/cost estimate. In particlular, For every stated lemma/theorem, the agent must estimate (1) the number of lines of a textbook proof, (2) the formalization difficulty on a 1--10 scale, and (3) the approximate USD cost assuming \$100/hour. This effort estimate assumes all previous algtop.tex results are already proved.

This prompt is repeatedly given to the agent until it converges in about 8 hours (producing 32 backups), announcing (after several debugging and double-checking runs) that it is not aware of any possible issues. The resulting file with the background theory and the newly created 230 definitions and 393 toplevel theorems (with the effort-based bounties) is then used as the start for our multi-agent autoformalization.

# Agent and Bounty Based Setup

We ultimately used four LLM agents (named Alice, Bob, Charlie and Dave), using two ChatGPT Pro Codex 5.3 models and two Claude Code (Opus 4.6 and Sonnet 4.6) models. Our setup is based on the rules of work and other settings described in  [@urban2026130klinesformaltopology]. In particular, we largely follow the CLAUDE.md rules file published there with similar agent workflow for a single agent, but we modify it for the agentic and bounty setting. The summary of these modified rules (234 lines) is as follows:

- Competitive--collaborative bounty system: Four agents compete for the theorem bounties (45k "simulated USD" tokens total) but are incentivized to collaborate to finish early and earn bonuses. Agents can issue sub-bounties, solve others' bounties, and strategically choose between cooperation and competition to maximize total and personal earnings.

- Locking and earning mechanics: Agents can lock a theorem by paying 10% of its bounty (max 10 locks, 24h each), reserving the right to collect the full bounty if completed. If someone else proves a locked theorem, the bounty still goes to the locker; expired locks must be removed, and balances can never go negative.

- Strict commit and ownership discipline: Agents must not modify others' locks, partial proofs, or sandboxes, and cannot change existing definitions/theorem statements. Frequent pull--commit--push cycles are mandatory, locks must be pushed immediately, and guard tools must confirm no rule violations before committing.

- Strategic focus and safety rules: Prioritize major theorems over exercises (better financial and project impact), avoid reverting or losing work, and never edit outside the AlgTop section. Progress should be continuous, incremental, and carefully merged to prevent destructive conflicts or wasted effort.

**Guard Scripts:** To enforce correct handling of balances, bounties, and locks, we use local guard scripts that agents must run before committing. The initial lightweight version checked core invariants (non-negative balances, positive bounties, at most 10 locks per agent, lock expirations within 24 hours, and basic bounty collection rules), but relied on relatively naïve line-based parsing, which allowed certain edge-case violations. A later stream-based version tokenizes the entire file, enforces immutability of definition and theorem statements (while allowing proof modifications), precisely tracks `Qed` vs. `Admitted`, validates lock persistence and expiry more robustly, checks balance transitions, and prevents misuse of keywords inside comments. The script is intentionally run locally rather than as a blocking git hook, permitting coordinated structural changes when needed. After resolving minor time-zone-related lock inconsistencies, the improved script has been functioning reliably.

# Formalization Growth and Collaborative Aspects {#s:charliecheat}

The formalization of the proofs with multiple agents started at about 8pm on Feb 16, with about 19k normalized lines[^2] of the previous library (mostly set theory and topology). By Feb 19, 11am, (2 days and 15 hours later) this number of lines has reached 121k. I.e. the four agents jointly produced about 39k lines per day. We have compared these numbers with the publicly available numbers from the General Topology project as of Feb 19, 2026[^3] The general topology project has reportedly been then running for about 60 days, reaching about 406k normalized lines, i.e. about 7k lines per day on average (using however only a single agent). This is only a rough comparison, one should also be looking at the capability to prove major theorems (Sect [6](#s:thms){reference-type="ref" reference="s:thms"}), etc. Still, this speed is encouraging.

Fig. [1](#fig:mg-growth-history){reference-type="ref" reference="fig:mg-growth-history"} shows the formalization size over the run of the experiment.[^4] The formalization grows mostly linearly with only very small local dips, mostly corresponding to refactoring done by the agents. In Fig. [2](#fig:history){reference-type="ref" reference="fig:history"}, the we see that the agents' balances rise overall. We have added Dave (4th agent) later, and had to reset Charlie's balance manually after it used a wrong Megalodon version, committing wrong theorems and collecting bounties incorrectly (this led us to tightening the framework). Cumulative bounties collected increased steadily across the agents, all agents locked some theorems throughout and most agents placed bounties on sub-lemmas they create.
```


## lit-oprover

Origin: `attached primary text:arxiv-2605-17283/extracted.md`

Whole-source SHA256: `073b7a2b9290802429feb9ccfc7f726bcaf8f1f8232571f6c5ced4327ddbe517`

Source lines: 9-39

```text
# Introduction

Formal theorem proving in systems such as Lean 4 [@moura2021lean4theoremprover] provides a rigorous setting for machine reasoning, where every step of a proof is mechanically verified by a small, trusted kernel. This makes them a natural foundation for reliable mathematical reasoning and verified software, but also imposes a high bar: a proof is accepted only if it is fully formal and type-correct. Recent prover systems built on Lean have substantially improved performance on challenging benchmarks such as MiniF2F [@zheng2021minif2f] and PutnamBench [@tsoukalas2024putnambench], yet absolute success rates on harder benchmarks remain low, and most systems still rely primarily on single-pass or best-of-$N$ whole-proof generation. Retrieval and compiler feedback, when used at all, are typically applied as test-time heuristics rather than as a proving policy that the prover is trained to use, leaving an important source of supervision largely unexploited.

A small but growing line of work has begun to incorporate retrieval, compiler feedback, and iterative repair into formal theorem proving [@yang2023leandojo; @jiang2022draft; @wu2025internlm2]. However, these capabilities are typically introduced as inference-time augmentations on top of a fixed prover, rather than as a learned policy that the model is trained to use. As a result, a prover trained mainly on finalized proofs sees compiler feedback and retrieved evidence only at deployment, in distributions it was never optimized for. Closing this train--inference mismatch requires training the prover to perform retrieval-grounded, feedback-conditioned refinement as part of its policy, not as a separate inference-time procedure.

Training such a policy in turn requires data that existing formal corpora do not provide. Public formal theorem proving corpora and proof-synthesis datasets [@wu2022autoformalization; @ying2024lean; @peng2025criticlean] focus on the end products of proving: large collections of formal statements and final compiler-verified proofs. In general, they omit failed attempts, retrieved context, and compiler diagnostics that drive proof repair in practice. Autoformalization and proof synthesis have greatly expanded the number of available statements and verified proofs, but they do not by themselves record the multi-round interaction histories needed to learn agentic self-correction. What is missing is therefore not more verified proofs, but corpora that explicitly preserve how proofs are constructed, fail, and get repaired.

In this paper, we present **OProver**, a unified framework for agentic formal theorem proving in Lean 4. Rather than treating retrieval, compiler feedback, and iterative repair as separate inference-time modules built on top of a fixed prover, OProver unifies them with training and data construction into a single proving framework. At inference time, OProver treats proving as a multi-round refinement loop, in which each failed proof attempt is revised using retrieved compiler-verified proofs and Lean 4 compiler feedback. At training time, the same retrieval and feedback signals shape the prover's policy: training proceeds in two phases, continued pretraining on Lean code and mathematics, followed by iterative post-training in which agentic proving, supervised fine-tuning, and reinforcement learning alternate. Newly verified proofs and repair traces produced by the current prover are recirculated into OProofs and the retrieval memory, so that the data, the training procedure, and the proving policy co-evolve within a single framework.

We pair OProver with **OProofs**, a large-scale corpus for agentic formal theorem proving that supports both pretraining and the co-evolution loop above. Unlike prior Lean datasets, which mostly preserve only final compiler-verified proofs, OProofs additionally records the trajectories of proof construction, failure, feedback, and repair. It contains 1.77M Lean statements and 6.86M compiler-verified proofs, paired with serialized proving trajectories that capture retrieved context, failed attempts, compiler feedback, and subsequent repairs. We build OProofs from three complementary sources: public Lean resources, large-scale proof synthesis with compiler verification, and traces from OProver's own agentic proving. The first two sources provide an initial corpus that supports both pretraining and post-training, while the third grows continuously as OProver improves: newly verified proofs are indexed into the retrieval memory and repair trajectories are added to subsequent training rounds.

In summary, our contributions are:

1.  **A unified framework for agentic formal theorem proving.** We propose OProver, which treats proving as a retrieval-grounded, feedback-conditioned refinement loop and trains the prover end-to-end to use these signals as part of its policy, rather than as test-time heuristics.

2.  **A large-scale corpus for agentic formal theorem proving.** We construct OProofs, containing 1.77M Lean statements, 6.86M compiler-verified proofs, and serialized proving trajectories that record retrieved context, failed attempts, compiler feedback, and subsequent repairs---supervision that prior Lean corpora do not provide.

3.  **A co-evolution pipeline between prover and corpus.** We develop an iterative post-training pipeline in which the current prover produces new verified proofs and repair trajectories: verified proofs are indexed into the retrieval memory, repair trajectories become SFT data, and the hardest unresolved cases provide RL signal for the next round.

4.  **State-of-the-art performance among open-weight whole-proof provers.** OProver-32B attains three best and two second-best results across five formal theorem-proving benchmarks, reaching Pass@32 of 93.3 on MiniF2F, 58.2 on ProverBench, and 11.3 on PutnamBench.

# Methodology {#sec:oprover}

Figure [2](#fig:oprover_overview){reference-type="ref" reference="fig:oprover_overview"} illustrates the three components of our framework. The **OProofs Construction** pipeline (top-left) builds a Lean-specific corpus from public Lean resources and raw informal sources, through deduplication, filtering, autoformalization, agentic proving, and Lean 4 verification (§[2.2](#sec:oproofs){reference-type="ref" reference="sec:oproofs"}). The **OProver Agentic Proving** pipeline (top-right) performs theorem proving as a multi-round interaction: given a target theorem, the prover policy queries a retrieval memory for top-$k$ compiler-verified proofs, produces a proof attempt, and is verified by the Lean 4 compiler; on failure, compiler feedback is returned to the policy and the proof is revised in the next round, while successful proofs are added back into the retrieval memory (§[2.1](#sec:oprover_framework){reference-type="ref" reference="sec:oprover_framework"}). The **OProver Agentic Training** pipeline (bottom) trains OProver in two stages: a one-time continued pretraining on OProofs yields a domain-adapted base model OProver-Base, followed by an iterative post-training loop in which the current prover performs agentic rollouts and is updated by SFT on round-level repair examples and RL on harder unresolved cases; verified proofs and repair trajectories from each iteration are folded back into OProofs and the retrieval memory, so that the corpus and the prover co-evolve across post-training iterations (§[2.3](#sec:training){reference-type="ref" reference="sec:training"}).

<figure id="fig:oprover_overview" data-latex-placement="t">
<embed src="pic/oprover.pdf" />
<figcaption> Overview of OProver. The framework has three components: <strong>OProofs Construction</strong> (top-left), which builds a Lean-specific corpus from public Lean resources and autoformalized statements; <strong>OProver Agentic Proving</strong> (top-right), which performs multi-round refinement under retrieval and Lean 4 compiler feedback; and <strong>OProver Agentic Training</strong> (bottom), where a one-time CPT yields OProver-Base, followed by an iterative post-training loop in which agentic proving, SFT, and RL produce <span class="math inline">OProver<sub><em>t</em> + 1</sub></span> from <span class="math inline">OProver<sub><em>t</em></sub></span>, while verified proofs are folded back into OProofs. </figcaption>
</figure>
```


## lit-circuit

Origin: `attached primary text:arxiv-2607-27259-circuitprover-reusable-proof-library/extracted.md`

Whole-source SHA256: `14c8dd97b4333dc77fd036a95dd054f4302156b4bd8620fa2c67cccda5c01f93`

Source lines: 52-61

```text
                                           Ablation studies show that accumulated proof knowledge re-           paradigm for improving productivity. As autonomous agents
                                           duces redundant proof construction across related verification       begin to participate in hardware generation (Yu et al.
                                           tasks, reducing proof length by 16.3% and verification time          2026), optimization (Fang et al. 2026), and debugging (Bai
                                           by 23.2%. These results show that reusable proof knowledge           et al. 2025), automated verification becomes increasingly
                                           can significantly reduce redundant proof efforts on related          important for validating their outputs and providing reliable
                                           verification tasks.                                                  feedback. However, ensuring functional correctness remains
                                                                                                                a major bottleneck (Yang et al. 2026). While simulation
                                                                                                                can detect many bugs, it cannot exhaustively cover all
                                                                  Introduction                                  possible execution behaviors, making formal verification
                                         The rapid growth of artificial intelligence is creating                indispensable for modern hardware development.
```


## lit-halmos

Origin: `attached primary text:halmos-how-to-write-mathematics/extracted.md`

Whole-source SHA256: `4eed1ca74206d5cc2c6cacb4ce405af7122f380195568f9aec984956a0062f2a`

Source lines: 239-284

```text
reading that is necessary; a disadvantage is that it becomes tempting to
indulge in snide polemic comments and heavy-handed "in" jokes. It is
surely obvious what I mean by the disadvantage, and it is obviously bad;
avoid it. The advantage deserves further emphasis.
    The writer must anticipate and avoid the reader's difficulties. As he
writes, he must keep trying to imagine what in the words being written may
tend to mislead the reader, and what will set him right. Fil give examples
of one or two things of this kind later; for now I emphasize that keeping a
spécifie reader in mind is not only helpful in this aspect of the writer' s work,
it is   essential.
    Perhaps it needn't be said, but it won't hurt to say, that the audience
actually reached may differ greatly from the intended one. There is nothing
that guarantees that a writer 's aim is always perfect. I still say it's better
to hâve     definite aim and hit something else, than to hâve an aim that is
            a

too inclusive or too vaguely specified and hâve no chance of hitting anything.
Get ready, aim, and rire, and hope that you'll hit a target: the target you
were aiming at, for choice, but some target in préférence to none.



                                      4.   Organize first

        The main      contribution that an expository writer can make is to organize
and arrange the material so as to minimize the résistance and maximize
the insight of the reader and keep him on the track with no unintended
distractions. What, after ail, are the advantages of a book over a stack of
reprints? Answer: efficient and pleasant arrangement, emphasis where
emphasis    needed, the indication of interconnections, and the description
                is

of the examples and counterexamples on which the theory is based in one     ;




word, organization.
   The discoverer of an idea, who may of course be the same as its expositor,
stumbled        helter-skelter, inefïiciently, almost at random. If there
                 on    it
were no way to trim, to consolidate, and to rearrange the discovery, every
student would hâve to recapitulate it, there would be no advantage to be
gained from standing "on the shoulders of giants", and there would never
be time to learn something new that the previous        génération did not
```


## lit-mathlib

Origin: `attached primary text:mathlib-community-2020-lean-mathematical-library/extracted.md`

Whole-source SHA256: `6719ec692860fa9d387aa6d30622424df2c8044a5d246a17d57d0b4df58eeaf0`

Source lines: 3-27

```text
Abstract                                                                                This paper describes mathlib, a formal library developed
This paper describes mathlib, a community-driven effort                              for the Lean proof assistant [20]. As a community-driven
to build a unified library of mathematics formalized in the                          effort with dozens of contributors, there is no central organi-
Lean proof assistant. Among proof assistant libraries, it is                         zation to mathlib; it has arisen from the desires of its users
distinguished by its dependently typed foundations, focus                            to develop a repository of formal mathematical proofs. We
on classical mathematics, extensive hierarchy of structures,                         are certainly not the first to profess this goal [1], nor is our
use of large- and small-scale automation, and distributed or-                        library particularly large in comparison to others. However,
ganization. We explain the architecture and design decisions                         its organizational structure, focus on classical mathematics,
of the library and the social organization that has led to its                       and inclusion of automation distinguish it in the space of
development.                                                                         proof assistant libraries. We aim here to explain our design
                                                                                     decisions and the ways in which mathlib has been put to
CCS Concepts • Mathematics of computing → Mathe-                                     use.
matical software; • Security and privacy → Logic and veri-                              In contrast to most modern proof assistant libraries, many
fication.                                                                            of the contributors to mathlib have an academic background
Keywords Lean, mathlib, formal library, formal proof                                 in pure mathematics. This has significantly influenced the
                                                                                     contents and direction of the library. It is a goal of many
ACM Reference Format:                                                                in the community to support the formalization of modern,
The mathlib Community. 2020. The Lean Mathematical Library.                          research-level mathematics, and various projects discussed
In Proceedings of the 9th ACM SIGPLAN International Conference                       in Section 7.2 suggest that we are approaching this point.
on Certified Programs and Proofs (CPP ’20), January 20–21, 2020,
New Orleans, LA, USA. ACM, New York, NY, USA, 15 pages. https:
//doi.org/10.1145/3372885.3373824                                                    1.1   A History of mathlib and Lean 3
                                                                                     The Lean project was started by Leonardo de Moura in
1     Introduction                                                                   2013 [20]. Its most recent version, Lean 3, was released in
Since the first mechanized proof-checking systems were re-                           early 2017 [22]. A new version is under development [57].
```


## lit-alpha-math

Origin: `attached primary text:arxiv-2511-02864-alphaevolve-mathematical-exploration-at-scale/extracted.md`

Whole-source SHA256: `e88bd7878b6def1b80e79a546655606540a5ef954ffab351e58da199cc525e3b`

Source lines: 9-33

```text
                                                   A BSTRACT. AlphaEvolve, introduced in [224], is a generic evolutionary coding agent that combines the generative
                                                   capabilities of LLMs with automated evaluation in an iterative evolutionary framework that proposes, tests, and refines
                                                   algorithmic solutions to challenging scientific and practical problems. In this paper we showcase AlphaEvolve as
                                                   a tool for autonomously discovering novel mathematical constructions and advancing our understanding of long-




arXiv:2511.02864v3 [cs.NE] 22 Dec 2025
                                                   standing open problems.
                                                       To demonstrate its breadth, we considered a list of 67 problems spanning mathematical analysis, combinatorics,
                                                   geometry, and number theory. The system rediscovered the best known solutions in most of the cases and discovered
                                                   improved solutions in several. In some instances, AlphaEvolve is also able to generalize results for a finite number
                                                   of input values into a formula valid for all input values. Furthermore, we are able to combine this methodology
                                                   with Deep Think [149] and AlphaProof [148] in a broader framework where the additional proof-assistants and
                                                   reasoning systems provide automated proof generation and further mathematical insights.
                                                       These results demonstrate that large language model-guided evolutionary search can autonomously discover math-
                                                   ematical constructions that complement human intuition, at times matching or even improving the best known results,
                                                   highlighting the potential for significant new ways of interaction between mathematicians and AI systems. We present
                                                   AlphaEvolve as a powerful tool for mathematical discovery, capable of exploring vast search spaces to solve complex
                                                   optimization problems at scale, often with significantly reduced requirements on preparation and computation time.
```
