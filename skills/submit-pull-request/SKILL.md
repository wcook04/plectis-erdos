---
name: submit-pull-request
description: Prepare, validate, commit, and, only when explicitly authorised, push and open a pull request that returns a mathematical, architecture, exposition, or clone-experience contribution to the public repository.
---

# Submit a pull request

A pull request asks the upstream repository to pull a proposed branch from a
contributor's fork. Use this skill when a contributor wants an agent to turn
finished work into a reviewable return. Preparation is local. Pushing a branch
and opening the pull request are external actions and require explicit
authorisation at that point.

## Establish the return boundary

Read `CONTRIBUTING.md`, `.github/PULL_REQUEST_TEMPLATE.md`, and the affected
subsystem's instructions. Record the public starting commit, contributor name
or handle, requested credit roles, material collaborators, tool and model
roles, evidence, and the strongest statement that remains unresolved.

Inspect rather than normalise the working tree:

```sh
git status --short
git branch --show-current
git remote -v
git diff --check
```

Do not discard, rewrite, or include unrelated changes. Do not expose private
paths, credentials, prompts, caches, or material outside the public clone.

Confirm that the recorded start belongs to the branch and inspect the original
delta:

```sh
git merge-base --is-ancestor <starting-commit> HEAD
git diff --stat <starting-commit>..HEAD
git log --oneline <starting-commit>..HEAD
```

Do not rebase merely because upstream has advanced. A pull request preserves
the branch history and compares it from a common ancestor. If current upstream
creates a real conflict, reconcile it deliberately and record that integration
work separately. Never rewrite a published contributor branch or force-push
without explicit authorisation.

## Make reviewable commits

Group changes by one coherent review question. Typical groups are:

- a mathematical source change and the focused evidence that validates it;
- the corresponding claim or exposition update after the mathematics is fixed;
- an architecture, tooling, or clone-experience repair and its tests; or
- builder-owned projections regenerated from an already included source.

Use separate commits when reviewers can accept or reject those groups
independently. Keep them together when splitting would hide the real invariant
or leave an invalid intermediate state. Do not create one commit per file by
ritual, and do not mix an unrelated cleanup into a mathematical claim.

Stage exact paths, inspect the staged set, and commit only what the contributor
owns:

```sh
git add -- <exact-paths>
git diff --cached --name-status
git diff --cached --check
git commit -m "<plain description of the coherent change>"
```

Never force-push, rewrite published history, or overwrite another contributor's
branch without a separate explicit instruction naming the exact target.

## Validate the proposed branch

The underlying release gate, `scripts/check_release.py`, consumes the supplemental
GitHub release checks from `scripts/check_ci_release.py`. Add release checks to
that registry so local committed-snapshot validation and GitHub run the same
commands; do not add workflow-only leaf checks. The cold preflight rejects
inventory drift. Preserve failure aggregation, optimized runs, and the separate
corpus-only privacy and publication boundaries. Keep admission deadlines large
enough for the complete bounded suite on a cold runner.

Repository maintainers must require the admission and first-contact statuses
as well as `build` and `release-surfaces` in GitHub branch protection. A skipped
dependent job can satisfy a required check; its failed upstream admission must
therefore be required itself. Preserve the GitHub Actions application binding
and strict current-base checks when updating protection.

Install the shared guard once for the repository, including its worktrees:

```sh
python3 scripts/check_push.py --install-shared
```

After committing, complete validation before opening a push connection:

```sh
python3 scripts/check_push.py --prepare HEAD
```

Use the pinned release interpreter provisioned by `scripts/run_release_check.py`.
If `scripts/check_release_ref.py` already passed all gates for that exact commit,
reuse its JSON receipt with `--prepare HEAD --release-receipt <path>`. The hook
only verifies the immutable commit, tree and validator identity against that
completed admission. A new commit or changed validator requires new admission;
a working-tree repair cannot certify an older outgoing ref. Never run the long
release suite inside the transport hook: idle SSH connections can expire before
validation finishes. Existing custom hooks are preserved.

For a stacked PR, pass its actual base when preparing:
`--base-ref refs/heads/<parent> --destination-branch <branch>`.
Otherwise the default is `refs/heads/main`. The hook observes that remote base
again during push. If it advanced, integrate it, regenerate affected projections
with their owners, commit, and validate again. A missing base object is fetched
without moving local refs, `FETCH_HEAD`, the index or worktree. GitHub validates
any base change after this observation.

Stage new source files before running inventory-based builders: their Git-backed
inventory intentionally excludes untracked files. Validate the committed snapshot
again after generation. Proof trust and repository shape also run in the cheap
preflight, before dependency provisioning or compilation.

After the final source and projection edits, run
`python3 scripts/refresh_projections.py --preflight` before preparing expensive
validation or pushing. It checks the shipped evidence without compiling or
installing anything. A valid local receipt does not establish that a fresh
clone has current evidence. Follow the named builder on failure and commit its
outputs and tracked receipt together. The full projection refresh also checks
artifacts requiring a separate Lean export and reports that exact repair command;
it must not silently declare them current or start an implicit Lean build.

Preflight derives its complete projection inventory from the refresh registry,
including reading editions embedded from experiment guides. After a Lean source
change, build and export with `python3 scripts/build_lean_dependency_index.py`
and commit both the index and tracked check receipt. If a local Lean environment
is unavailable, an explicitly authorised CI dispatch with scope
`dependency-index-refresh` builds the branch and exports its recovery artifact
even while the ordinary release gate rejects stale evidence. Download and
validate that artifact against the exact branch before committing it; the
recovery run never substitutes for a passing normal PR run.

The shared preflight also runs `scripts/check_ci_contracts.py`: the cold build,
cache, exporter, scheduling and push-guard suites, in normal and optimized
Python. Its coverage check rejects a test added to a build, external-verification,
cache-warm or coverage workflow without local admission coverage. Register new
infrastructure suites there. Keep scheduling policy in
`test_lean_workflow_environment.py`; callers must reuse its behavioral checks
instead of asserting a second, contradictory spelling of the workflow.

Run the narrow tests required by every changed subsystem, followed by the
public-boundary and contribution-entry checks when relevant. Record exact
commands, results, omissions, and environmental deferrals. A green test is
evidence about that test, not acceptance of a mathematical claim.

Run `skills/propagate-research-consequences/SKILL.md` before finalising the
return. The pull-request body should disclose any deferred downstream consumer
and its re-entry condition.

Review the complete branch diff against its intended base:

```sh
git diff --stat <base>...HEAD
git diff --check <base>...HEAD
git log --oneline <base>..HEAD
```

Prepare a pull-request body using the tracked template. It must say what
changed and why, what another person can check, what remains open or uncertain,
and who supplied each material contribution. Describe agent output as a
candidate until the relevant review has occurred.

## Stop before sending

Without explicit authorisation to publish, stop after the commits, validation
receipt, proposed title, and draft body are ready. Tell the contributor which
remote branch and upstream base would be used.

After explicit authorisation, push the named branch to the contributor's fork:

```sh
git push -u <fork-remote> <branch>
```

If GitHub CLI is available and authenticated, open the pull request against
the verified upstream repository and base. Otherwise return the fork URL,
branch name, proposed title, and body so the contributor can use GitHub's web
form. Never guess an account, remote, base branch, or repository identity.

Opening a pull request records a proposal. It does not mean that the patch is
accepted, that a formal statement matches its intended mathematics, that a
result is novel, or that an Erdős problem has been solved. Maintainer review,
accepted-receipt creation, public claim changes, Comparator, Palomar, and
external mathematical acceptance remain separate steps.

## Keep publication and local checkout state distinct

Before publication, after committing the intended candidate, run
`python3 scripts/check_checkout_sync.py --fetch --check-merge` (add
`--base origin/<target>` for a different target branch). Exit 1 names merge
conflicts; exit 2 means the check could not certify the candidate. Resolve
conflicts and rerun the release checks before pushing. This check preserves
the checkout and accepts a clean feature branch that differs from main; it
does not establish that the merged proofs or generated artifacts are valid.
Use `python3 scripts/check_checkout_sync.py --fetch` for a divergence report.
Read both directions of divergence: an old feature branch can contain useful
unmerged work while missing later public papers and fixes. Preserve it in a
separate worktree; do not use its generated files to overwrite current main.
Review the PR's exact head and failed checks before attempting reconciliation.

After an authorised merge, fast-forward the canonical local main checkout
with `python3 scripts/check_checkout_sync.py --sync-main`. Recheck the actual
remote head and record any remaining feature work separately. A successful
remote merge is not evidence that a different local checkout was updated.
Never reset or discard a branch or untracked files to obtain equality.
