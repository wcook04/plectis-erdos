# Erdős 1049 direction-search receipt

This directory reproduces the finite direction search reported in the long
Erdős 1049 paper.  The program evaluates the ratio
`theta_star = C0 / C1` from equations (25) and (26) of Wadim Zudilin's 2004
paper for every primitive integer direction in his cone whose four entries
are at most 30.  It is the public adaptation of the research probe used for
the manuscript; the formulas, admissible cone, and permutation observation
remain attributed there to Zudilin.

For source custody, the pre-publication probe from which this copy was adapted
has SHA-256
`d0cd58b0a72dc5bcc98fb237b2033962fb66cf18157d281bb7758852f416fef2`;
the public script in this directory is self-contained apart from mpmath.

Create an isolated environment and install the exact numerical dependency:

```bash
python3 -m venv /tmp/erdos1049-direction-search
/tmp/erdos1049-direction-search/bin/python -m pip install \
  -r research/experiments/erdos1049/requirements.txt
```

Recreate the tracked receipt from the repository root:

```bash
/tmp/erdos1049-direction-search/bin/python \
  research/experiments/erdos1049/direction_search.py \
  --bound 30 \
  --output research/experiments/erdos1049/receipts/direction-search-bound30.json
```

To verify the tracked bytes without overwriting them, add `--check`:

```bash
/tmp/erdos1049-direction-search/bin/python \
  research/experiments/erdos1049/direction_search.py \
  --bound 30 \
  --output research/experiments/erdos1049/receipts/direction-search-bound30.json \
  --check
```

The search visits 37,533 primitive directions.  The cone inequalities,
primitive normalization, rational breakpoints, step-function weights, and
`C1` are computed exactly.  The trigamma values and pi in `C0` are evaluated
with mpmath 1.3.0 at 30 decimal digits.  The receipt therefore reproduces the
reported bounded numerical evidence, including the tied leading directions
`(14,12,14;27)` and `(15,12,13;26)`.  It is not an interval-certified proof
of their order, and it makes no claim about a larger box or the whole cone.
