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

Run the narrow tests required by every changed subsystem, followed by the
public-boundary and contribution-entry checks when relevant. Record exact
commands, results, omissions, and environmental deferrals. A green test is
evidence about that test, not acceptance of a mathematical claim.

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
