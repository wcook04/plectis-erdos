# Exact FC1041 sharp-gap adapter verification

This package asks the pinned official Palomar mechanical verifier to check the
original `FC1041SharpGap` module against the complete statement in Formal
Conjectures PR 6576 at `43874b729c11b65783050871577a22f9093362a8`.
The original adapter and its four imported project source files remain byte-for-byte
identical to `c45de9aab30cf25172040c94c60987dec46645d8`.
`Challenge.lean` imports only Mathlib and repeats the exact FC statement,
renaming its declaration to the original proof's full name for Comparator.
The Challenge's deliberate `sorry` supplies the trusted statement; the
Solution is the original adapter and contains no admitted proof.

`source-binding.json` binds the proof closure, pinned dependencies, challenge,
configuration, metadata and Lake library registration. The caller freezes
that manifest's digest, selects only the adapter, permits only `propext`,
`Classical.choice` and `Quot.sound`, and enables NanoDa. A passing completed
full mechanical report is required before claiming independent verification.
Dispatching the workflow or passing its selector is insufficient.

This is a mechanical preflight, without registry submission, registration,
mathematical peer review or approval of the upstream pull request. It does not
change the benchmark statement, paper result or scope of the parent question.
