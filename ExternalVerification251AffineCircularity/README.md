# Erdős #251: signed windows and two circular escape tests

This package exposes three exact recurrence-level endpoints.

First, under evenness of the difference digit, two adjacent unit windows with
a mismatch occur exactly in one of two signed configurations: digit `+2` with
the first shift in `(1/2,1)`, or digit `-2` with the first shift in
`(-1,-1/2)`. Thus the proposed adjacent certificate requires a prescribed
magnitude event, not merely unequal prime gaps.

Second, cofinal escape from the data-dependent affine cylinder

```text
tailShift(N+r) ∈ -block(N,r) + 2^(r+1) ℤ
```

is equivalent, under even difference digits, to non-eventual integrality of
the base shift. The block cancels after substitution of the recurrence, so
this condition supplies no independent arithmetic input.

Third, even the non-adaptive fixed-lattice version is equivalent to the same
non-eventual-integrality conclusion whenever the terminal shifts obey the
stated bound and that bound is dyadically dominated. This is an exact second
circularity theorem, not a prime-specific producer.

Erdős #251 remains open: none of the three theorems proves the required event
for the actual consecutive-prime-gap orbit. The separate LCM-diagonal and
polynomial-countermodel packages cover the other strongest endpoint families.

The deliberate negative changes the signed normal form by deleting its
negative branch, and also omits the two circularity declarations, so
Comparator must reject it.

Focused Lean elaboration and the axiom audit are presently deferred: the
guarded builder returned typed exit `75` before proof checking because free
disk was below its 17.18 GB safety floor. This is a capacity receipt, not
proof evidence; the exact package targets must be rerun after storage is
cleared.
