<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Exact finite checks

For every one of the 2,496 first-escape windows with `B≤97`, `gcd(B,30)=1`,
and starts 1–96, a successful length at most 10 is recorded. These are finite
certificates, not a cofinal escape or irrationality theorem.

Python 3.10 or later and the standard library suffice. Run without `-O`: the two inherited checkers use assertions. No network or formal prover is invoked.

```sh
python3 check_structures.py --n 256 --output exact_checks.json
python3 check_new_lemmas.py --n 256 --output new_ordinary_checks.json
python3 check_pass2.py --output-dir .
python3 verify_certificates.py pass2_certificates.json
```

The first two scripts reconstruct the literal shell sequence and independently count 781,832 weighted triangle terms over 256 shells. Their remaining diagnostics include finite shift identities and exact carry ansatz failures, not an assertion about every eventual polynomial or every fixed operator.

`pass2_certificates.json` contains the no-crossing cubic row counts and all 2,496 first-escape window witnesses for `B≤97`, `gcd(B,30)=1`, starts 1–96, maximum allowed length 24. Observed first lengths are 1–10. `verify_certificates.py` does not import the producer: it checks the cubic row endpoints with integer powers, reconstructs shell data with a separate enumeration and verifies the declared grid is complete. It checks first-success claims, not only success at a chosen length.

`check_pass2.py` also checks 25 exact strip decompositions, 14,000 synthetic rational-denominator cases, 125 onset fixtures, 150 direct-recoding indices and 3,900 explicit defect bounds. Six altered certificates must be rejected. Synthetic rational tests are algebraic fixtures, not approximations asserting the target scalar is rational.

`execution_receipt.json` records the commands actually run, runtime/version information, source hashes and output hashes. Output regeneration changes no manuscript and publishes nothing. The historical large scan and two missing large exclusion witnesses were not rerun or recreated. No finite output proves the cofinal escape statement or irrationality.
