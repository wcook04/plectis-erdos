<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Reproduce the Erdős 251 computations

These programs reproduce the three finite computations cited in the
[prime-gap reasoning paper](../../../paper/251/erdos251-prime-gap-reasoning-surface.tex).
The first uses integer brackets to compute a continued-fraction denominator
bound. The other two count events in finite ranges of prime-gap tails. They
do not prove irrationality or a statement about every sufficiently large
index. The Python programs do not run Lean.

Use Python 3.11 or newer. From the repository root, this command reruns the
paper's complete 80,000-bit continued-fraction calculation and compares its
output with the saved result. It needs only the Python standard library:

```sh
python3 research/experiments/erdos251/replay.py
```

Expect `matched_recorded_result: true`. The run took about four seconds on
the maintainer's machine. The saved result has 23,369 partial quotients;
the paper explains how its integer bracket supports the finite denominator
bound. A smaller, editable example prints the calculation directly:

```sh
python3 research/experiments/erdos251/certified_continued_fraction.py --scale-bits 512
```

## The other recorded runs

| Case | Recorded range | Arithmetic | Observed replay time |
| --- | --- | --- | --- |
| [Continued fraction](receipts/certified-cf.json) | 80,000 bits | Integer bracket and convergents; diagnostic statistics use floats | 4 seconds |
| [Adjacent mismatch](receipts/adjacent-mismatch.json) | Primes below 120 million; offsets 1–16 | Integer sieve, float64 tails and comparisons | 8 seconds |
| [Free pairs](receipts/free-pair.json) | Primes below 20 million; moduli 1–20 | Floating-point event counts; integer denominator check | 11 seconds |

These timings describe one machine. The larger scans can use several hundred
megabytes of memory. A positive floating-point event count is a numerical
observation; it is not an individually certified witness or a proof of
cofinality. The continued-fraction and denominator checks rely on the analytic
tail bounds explained in the paper.

The free-pair replay also uses only the standard library:

```sh
python3 research/experiments/erdos251/replay.py --case free-pair
```

The adjacent-mismatch scan needs the pinned NumPy dependency. Install it in a
virtual environment, then run the scan with that environment's interpreter:

```sh
python3 -m venv .venv-computations
.venv-computations/bin/python -m pip install -r research/experiments/erdos251/requirements.txt
.venv-computations/bin/python research/experiments/erdos251/replay.py --case adjacent-mismatch
```

`--case all` runs the three cases sequentially. Integer results must match
exactly; diagnostic floating-point values use relative and absolute tolerance
of `1e-12` to allow platform rounding. A mismatch exits with code 1 and names
the first differing fields. `--timeout` changes the default five-minute limit
per case. `--check` checks the saved program hashes and receipt shape without
rerunning the computations.

## Change an input or report a discrepancy

Each program has `--help` and accepts explicit range or precision arguments.
Changing those arguments computes a different finite experiment. It does not
update the saved paper result. Include the command, output, Python version,
and any NumPy version when reporting a discrepancy through the repository's
[contribution route](../../../CONTRIBUTING.md).

Will Cook authored the original programs. [Source provenance](source-provenance.json)
records their original hashes; the public copies clarify usage and finite
evidence labels. Each saved receipt binds the public program bytes and exact
arguments. Code and computation data use Apache-2.0; the manuscript uses
CC-BY-4.0. A match with a saved run is reproducibility evidence, not independent
mathematical review.
