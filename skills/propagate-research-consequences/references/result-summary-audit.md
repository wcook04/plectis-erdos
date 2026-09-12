# Audit the strongest supported results from a cold clone

Use this procedure to review result summaries or choose the strongest
substantive progress for the requested problems. It needs Git, Python, and
tracked public files. It does not require a private system, a model's memory,
network access, or a full Lean build. Run additional proof checks when a
specific uncertainty warrants them; record their actual scope.

For an audit-only request, return proposed corrections and consumer
dispositions without editing. When repair is requested, apply the supported
corrections through their owners. Do not turn a review into a new research
campaign or publication request.

## Establish the evidence snapshot

```sh
git rev-parse HEAD
git status --short
python3 scripts/query_corpus.py --overview --format json
python3 scripts/query_corpus.py --papers
python3 scripts/query_corpus.py --route browse_claim_status
```

Record the inspected commit and any dirty input paths. On a shared checkout,
use a clean committed snapshot for the cold audit and keep proposed edits
separate. Do not silently pull, replace the checkout, or pretend an older
clone is current upstream. Read command help when the clone's CLI differs
from these examples.

The overview supplies the problem roster and entry handles. Its short card
and ranked signals are not an exhaustive candidate set or a certificate of
mathematical importance. For an all-problem request, keep every indexed
problem in the receipt, including those for which the available evidence does
not support a confident lead. Do not freeze today's roster in this skill.

## Reconstruct candidates before choosing a lead

For each requested problem, follow its claim, module, paper, and continuation
handles. Useful bounded drilldowns include:

```sh
python3 scripts/query_corpus.py --route erdos_<number>
python3 scripts/query_corpus.py --claim <claim-id>
python3 scripts/query_corpus.py --module <module>
python3 scripts/query_corpus.py --declaration <declaration>
python3 scripts/query_corpus.py --paper-source <source-path>
```

Use `query_route_memory.py --problem <number>` after selecting a continuation;
its canonical route is not the problem's full result inventory. Likewise a
paper-source card may list only registered anchors. Read the actual abstract,
status table, and theorem/proposition statements in the named short and
reasoning sources; when anchors are missing, search those named files for
theorem environments and labels. An unregistered ordinary theorem may be
stronger than every result in the machine ranking.

Compare `docs/RESULTS.md`, the relevant short and reasoning papers, the public
claim rows, and the source/results inventory reached by those handles. Look
for plausible stronger results absent from the guide or registered roster.
Once a problem directory or theorem is named, use targeted text search and
`git ls-files -- <scope>` to inspect tracked source. A query miss, missing claim
row, or missing Comparator entry is not proof that no theorem exists.

Group wrappers, equivalent statements, and routine corollaries into one
mathematical family. Compare candidates at their full strength, including
quantifiers and exceptional cases. Spend more evidence effort on plausible
lead replacements, contradictory descriptions, and changed proof status than
on already settled supporting lemmas. Account for the candidate scope read;
do not describe a short ranked query as a review of every theorem.

## Separate mathematical reach from evidence

For each serious candidate, write its proposition in ordinary mathematical
language and classify what it contributes:

| Logical role | Question that distinguishes it |
|---|---|
| Proved case or partial resolution | On exactly which inputs does it establish the original target? |
| Useful sufficient reduction | Which burden has been discharged, and what distinct sufficient task remains? |
| Necessary condition | What would a counterexample or hypothetical rational branch have to satisfy? |
| Exact reformulation | Is the remaining condition still equivalent to the original target? |
| No-go or countermodel | Which hypotheses or proof architecture does it exclude? |
| Independent result | What theorem does it establish even though the original endpoint stays open? |
| Finite exclusion | What finite range is certified, and why does that not supply a cofinal statement? |

An implication or an `iff` alone does not establish a useful reduction. Name
the work removed. A target-equivalent coordinate system may be useful, but its
existence does not discharge the equivalent open proposition. A necessary
rank-growth condition is not an endpoint contradiction without the incompatible
upper bound. A synthetic countermodel does not become the actual prime,
totient, or other distinguished sequence. A common-denominator result does
not automatically control cancellation in a reduced denominator.

Record evidence on a separate axis: ordinary argument, cited input, checked
Lean theorem, source-only formalisation, finite computation, or open
inference. For a Lean claim, locate the exact declaration and assumptions;
inspect the public receipt or scoped replay that supports the reported check.
Source presence, a successful import search, or a wrapper that assumes the
missing conclusion is not a successful proof replay. Compare receipts with
the actual source bytes and toolchain. An old header saying "uncompiled" does
not override a valid later receipt, and an old passing receipt does not check
edited source. Do not launch a whole-library build to answer a local evidence
question.

For ordinary mathematics, inspect the load-bearing argument and the cited
inputs at the relevant scope. State whether the pass checked source,
reconstructed the argument, or obtained independent review. A finite checker
may support an identity or falsify an example; it does not certify an
all-degree or all-rank theorem. Preserve attribution independently of value:
formalising a previously stated theorem can be substantial work without
creating theorem priority.

## Choose and explain the best supported selection

Prefer results by what they actually prove or eliminate: logical reach,
mechanism, independence, sharpness, reusable consequences, and the live
remaining burden. Neither theorem counts, numerical record size, recency,
query order, nor ease of validation makes that judgment.

Keep incomparable results visible. One problem may deserve both an
unconditional standalone theorem and a useful target-directed reduction;
another may have two partial regimes neither contains. Explain the selection
against the strongest alternatives, rather than forcing a single scalar rank.
Distinguish a stronger conclusion from a better formalisation of the same
conclusion. If bestness is unresolved, report that uncertainty and the exact
comparison needed.

Write the result first, then what it achieves, its evidence, and its remaining
boundary. A useful summary answers: what was proved, why it matters, and what
has still not been supplied. A missing registry row is a registration gap,
not a reason to bury an independently inspected public argument. Such a result
can be described with its actual evidence class and missing registration
stated; it cannot be presented as an already reviewed registry claim. A real
contradiction between the source and registry needs authority repair before
changing the public claim status.

## Propagate through the right owners

For every affected consumer, record **update**, **verified unchanged**,
**defer with owner and re-entry condition**, or **outside scope**. Include
result guides, overview/ranking metadata, claim and open-proposition records,
short and reasoning papers, entry prose, source comments, and release copies
when they actually depend on the selection. Use
`skills/public-mathematical-writing/SKILL.md` for authored mathematics and the
named builders for generated indices, full-text mirrors, and packets. Do not
hand-edit generated copies or invent a second authoritative ranking file.

Bind publication separately from local correctness. For every newly promoted
result, retain the public source path, declaration or theorem anchor, inspected
commit and source hash. If another commit will be published, check the source
and links **at that commit**, for example with `git show <commit>:<path>`.
A file present in today's working tree may be absent from the release. Do not
call a local edit published, or restamp a website mirror before its source
publication has landed. Use the existing return and submission skills for
integration; ordinary audit authority does not itself authorise a push.

For a small set of selected files, this portable command binds hashes to
committed bytes rather than whatever happens to be in the worktree:

```sh
python3 - <commit> <source-path> [<source-path> ...] <<'PY'
import hashlib, json, subprocess, sys
revision = subprocess.check_output(
    ["git", "rev-parse", "--verify", sys.argv[1] + "^{commit}"], text=True
).strip()
rows = []
for path in sys.argv[2:]:
    content = subprocess.check_output(["git", "show", revision + ":" + path])
    rows.append({"path": path, "sha256": hashlib.sha256(content).hexdigest()})
print(json.dumps({"commit": revision, "sources": rows}, indent=2))
PY
```

Use exact tracked paths discovered above. A missing object is an evidence
failure to resolve, not a reason to substitute a newer file silently.

## Validate and leave a reusable receipt

Run the checks relevant to what changed. For skill/routing changes:

```sh
python3 scripts/agent_skill_catalog.py
python3 scripts/agent_skill_catalog.py --check
python3 scripts/test_agent_entry.py
python3 scripts/test_compact_agent_entry.py
python3 scripts/check_cold_clone_comprehension.py --quick
```

For result prose, check exact source correspondence and links at the selected
revision, then the writing/publication checks named by its owner. Keep new
failures separate from known unrelated failures; never weaken an evidence
check merely to make the pass green.

The pass receipt should contain the inspected revision and scope, candidate
families considered, per-problem selection and alternatives, exact theorem
and logical role, evidence source/hash and check scope, discharged and open
burdens, changed consumers, validation, and deferred publication work. It is
an audit record, not a new proof authority. Reuse the existing research-return
package when the audit is being contributed upstream.

Repeat the discovery route from a clean start after repairs. When an
independent agent is available and authorised, give it the clone and the
request without the intended ranking. Compare its actual result with the
source-backed selection. Feed demonstrated misses back into this procedure,
its routing, or the responsible checker; do not add speculative universal
rules or require delegation for every routine pass. Re-audit changed results
and their consumers when statements, evidence, or publication inputs change.
