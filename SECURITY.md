<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Security

This repository is a static scholarly artefact: Lean sources, a paper, and
release metadata. It ships no service, network code, or credentials, so the
realistic security surface is the build toolchain and the repository
configuration.

## Before you run anything

Cloning downloads tracked files but does not run this project's Python or Lean
code. The repository defines no submodules, Git LFS filters, or repository
hooks. You can use the reader sparse checkout in the README to inspect the
papers, claim records, open boundaries, and source map before executing a
project command.

The trust boundary changes when you run code. The read-only query commands
execute tracked Python. A Lean build also installs or invokes the exact Lean
toolchain in `lean-toolchain` and the Mathlib revision in `lake-manifest.json`.
Release-only Python packages are version- and hash-pinned in
`requirements-release.txt`, and GitHub Actions dependencies are pinned to full
commit hashes. The release workflow checks for prohibited proof shortcuts,
private path leaks, stale generated evidence, and suspect material reachable
through Git history.

No repository can guarantee that executing unfamiliar code is risk-free. If
you need to treat the checkout as hostile, inspect the commit and lock files
first and run it in a disposable virtual machine or container with no secrets
or write access to important files. A green Lean build establishes proof
checking for the imported declarations; it is not a general security audit.

Report privately via GitHub Private Vulnerability Reporting:

```text
https://github.com/wcook04/plectis-lean-erdos249-257/security/advisories/new
```

Use it for anything sensitive: a supply-chain concern in the pinned
toolchain or dependencies, a CI configuration issue, or leaked material that
should not be public. Do not open a public issue with sensitive details.
Mathematical errors and build failures are not security issues; use the
ordinary issue forms for those. Reports get a best-effort response from a
solo maintainer, normally within a week.
