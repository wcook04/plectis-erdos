<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Formal source

The [package configuration](../lakefile.toml) assigns these files to two default
libraries. [Erdos249257](Erdos249257.lean) contains shared machinery from the
original two-problem development; [ErdosProblems](ErdosProblems.lean) provides
problem-specific statements. The historical namespace remains a public import
interface. Find an argument through the [source map](../docs/reference/SOURCE_MAP.md),
or start from its [paper](../paper/README.md).

The compact roots do not import every auxiliary module. The
[coverage workflow](../.github/workflows/lean-coverage-build.yml) records the
additional build targets. Selected verification packets, the large #251 certificate and downstream
examples have separate source directories and non-default Lake targets in
`lakefile.toml`; their placement does not change their Lean module names.

Use [Reproducibility](../docs/REPRODUCIBILITY.md) for toolchain and build commands,
and [AGENTS.md](../AGENTS.md) before editing. A source file's presence or an
index entry is not proof of a successful build. Public statement status and
remaining assumptions belong to [the claim records](../docs/claims.json).
