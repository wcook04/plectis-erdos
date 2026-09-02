# Erdős #269: pinning and rigidity of the actual integral branch

This package exposes the strongest source-current analysis of the one branch
left open by the actual-shell-orbit dichotomy.

The strongest endpoint is orbit rigidity: any real orbit following the same
recurrence indefinitely inside common windows of width `w(A+k) = o(2^k)` must
equal the genuine infinite tail at its initial index. Thus an integer seed
surviving all exact windows is not a finite-recursion artefact; it is the
actual integral branch.

The genuine state also has an exact finite-depth mixed-radix expansion:

```text
X_m = sum_(i<K) d_(m+i) / product_(j<=i) b_(m+j)
      + (H(2^m)/2) T_(m+K).
```

This is an identity for the actual infinite source tail, with its remainder
displayed exactly. At depth one it refines the pinning form

```text
X_a = d_a / b_a + X_(a+1) / b_a.
```

and one integral state makes every later state integral.

These theorems do not show that no integral seed survives, and hence do not
prove irrationality or transcendence for the three-prime running-LCM series.
They form one coherent structural candidate subordinate to the actual-shell
orbit and all-scale rationality-lattice packages.

The deliberate negative deletes the future-state term from the pinning
identity and omits the exact telescope and two rigidity declarations, so
Comparator must reject it.

The original three-endpoint package remains without a terminal focused receipt;
the newly exposed telescope makes fresh four-endpoint source, wrapper, and
axiom validation mandatory. Capacity deferral is not proof evidence.
