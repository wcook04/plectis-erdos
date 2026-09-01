---
name: lean-concurrent-validation
description: Run Lean validation from one or more public cold clones without duplicate builds, competing build writers, manual retry supervision, or private infrastructure.
---

# Concurrent Lean validation

Use this skill for Lean builds, focused module checks, changed-source checks,
cache hydration, or a trace where two agents appear ready to compile. The
implementation is entirely tracked in this public repository. It does not
require `ai_workflow`, a sibling checkout, a service, or private host setup.

## Plan cheaply, execute through the shared owner

A plan reads the local graph and does not compile:

```sh
python3 scripts/lean_fast_build.py --plan --changed-from HEAD
```

Normal execution automatically submits or joins an exact validation future:

```sh
python3 scripts/lean_fast_build.py --jobs 2 <module-or-lean-path>
python3 scripts/lean_fast_build.py --jobs 2 --changed-from <git-ref>
python3 scripts/lean_fast_build.py --jobs 2
```

Equivalent Lean source, toolchain, manifest, configuration, target, and command
inputs produce the same semantic key across clones on the same host; unrelated
paper and README edits do not defeat reuse. One
detached owner runs; followers consume the same in-flight or terminal receipt.
Different Lean validations queue behind one `lean-host` resource lock, so a
focused check cannot race a root check or another clone's build.

The owner also prepares `.lake/packages` through
`scripts/lean_package_share.py`. The first compatible checkout publishes an
immutable host seed with copy-on-write cloning; later cold clones receive an
independent package path backed by the same physical blocks. Existing clean,
same-lock clones reconcile once. Mutable package trees are never symlinked,
dirty dependency repositories are preserved, and an ordinary byte-for-byte
copy is never used as a fallback. On a filesystem without copy-on-write clone
support, the build remains local and correct without claiming disk sharing.
After a successful admitted build on macOS, large repeated Lake
`*.setup.json` manifests are transparently compressed only after a byte-for-byte
hash check and a source-generation recheck. Obsolete semantic package seeds
are bounded to two. Neither operation changes source or proof authority.

Inspect the package decision without mutation when diagnosing a clone:

```sh
python3 scripts/lean_package_share.py --plan
```

The plan and apply paths use the same symlink, semantic-lock, repository
cleanliness, completeness, liveness, and filesystem boundaries.
To run only the byte-preserving setup-manifest compactor:

```sh
python3 scripts/lean_package_share.py --compact-setup
```

Do not bypass this boundary with raw `lake build`, `lake env lean`, background
shells, or a second build wrapper merely because a result is pending. `--jobs
2` bounds dependency-wave batches inside the single admitted owner; it is not
permission for two top-level builds.

## Detached and resumable operation

To start work without attaching the current shell:

```sh
python3 scripts/validation_singleflight.py submit --class lean \
  --target <module-or-lean-path>
```

The JSON receipt contains the key. `status --key <key>` is read-only;
`collect --key <key> --wait` is the explicit resume path. The `run` subcommand
combines submit-or-join with collection. If an agent or terminal disappears,
the detached owner continues. Reissuing the exact build command joins or
reuses it. If the host externally terminates a Lean child with SIGTERM or
SIGKILL, the same owner automatically resumes the partial build up to three
bounded attempts. Exhaustion becomes exit `75`, with the last signal exit kept
in the receipt; it is never reported as a theorem failure. No person must
recreate the build or supervise a retry loop.

## Storage and evidence boundary

The default state root is a repository-identity directory under the host's
platform cache (`$XDG_CACHE_HOME`, `~/Library/Caches`, or `~/.cache`). This is
what lets equivalent cold clones share. Set
`VALIDATION_SINGLEFLIGHT_STATE_ROOT` only for deliberate isolation.

Persistent stdout and stderr retain bounded tails. Terminal state is cleaned
automatically at most once per hour under the seven-day/one-GiB/ten-thousand-
inode policy; manual `cleanup` uses the same safety checks. Job locks use 256
stable buckets, so unique validation keys do not create an unbounded lock-file
population.

Singleflight, cache state, a seed, and a queue receipt are acceleration and
coordination—not mathematical evidence. Only a terminal receipt preserves the
underlying validator's exit code. Exit `75` means unavailable or deferred, not
a Lean theorem failure; a nonzero Lean/Lake exit remains a validation failure.
