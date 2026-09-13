<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Use the library in another Lean project

Match this checkout's `lean-toolchain` in your project. In your project's
`lakefile.toml`, add the dependency below alongside your own package and target
declarations. The package name is `erdos249257`; the repository name is
`plectis-erdos`.

```toml
[[require]]
name = "erdos249257"
git = "https://github.com/wcook04/plectis-erdos.git"
rev = "d59af724cc30a1fb87c4c105807255fa366b0bde"
```

This pins an accepted public revision. Choose a different full commit hash
deliberately when upgrading, and use that revision's toolchain and dependency
lock. A floating `main` revision does not preserve a reproducible input.
Then import the library in your Lean file:

```lean
import Erdos249257
import ErdosProblems
```

From your project, fetch the pinned dependencies, obtain their Mathlib cache,
and build the two imported library targets:

```sh
lake update
lake exe cache get
lake build @erdos249257/Erdos249257 @erdos249257/ErdosProblems
```

Your project's normal Lake build can then check your own files. The first
build still needs the Lean and Mathlib space described in [the build prerequisites](REPRODUCIBILITY.md#2-reproduce-the-pinned-lean-environment). For
local development, replace the `git` and `rev` fields with
`path = "../plectis-erdos"`, adjusted to your checkout's location.

To verify the package boundary using an already built clone, run from this
repository after the [complete build](REPRODUCIBILITY.md#2-reproduce-the-pinned-lean-environment):

```sh
python3 scripts/check_downstream_reuse.py
```

This creates a separate temporary Lake project, adds this checkout as a path
dependency, and checks an unchanged copy of the consumer examples through
Lake's package resolution. It reuses the prepared dependency files and runs
under the same host build lock. It does not fetch another copy of Mathlib or
claim that an absent build cache is a successful check. CI runs this check
after building the libraries and examples.

