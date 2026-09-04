# Sturmian Hecke–Mahler transfer: the direct route is destroyed by divisor shifts

- Script: `formal_math/erdos257_period_noncollapse/scripts/sturmian_divisor_shift_probe.py`
- Receipt: `state/formal_math/erdos257_period_noncollapse/sturmian_divisor_shift_receipt.json`
- Literature boundary: Bugeaud–Laurent,
  [arXiv:2203.12901](https://arxiv.org/abs/2203.12901), Theorem 1.1; Luca–Ouaknine–Worrell,
  [arXiv:2412.07908](https://arxiv.org/abs/2412.07908).

## Why this was worth testing

For a Sturmian support word `a_n`, put

    H_A(z) = sum_(n>=1) a_n z^n.

Bugeaud and Laurent prove that a power series with Sturmian integer coefficients
takes transcendental values at every nonzero algebraic point in the unit disc.
The Erdős-257 value is not one such value. It is

    S(A) = sum_(n in A) 1/(2^n-1)
         = sum_(r>=1) H_A(2^-r)
         = sum_(m>=1) tau_A(m) 2^-m,                (1)

where `tau_A=1*a` is the divisor transform. Individual transcendence of every
`H_A(2^-r)` does not decide the infinite sum in (1).

The Hecke–Mahler proofs exploit the exceptional additive near-periodicity of a
Sturmian word: if `q_k` is a continued-fraction denominator of the slope, the
defect `a_(m+q_k)-a_m` is supported on a set of density tending to zero. The
probe asks the exact transfer question: does the same convergent shift remain
sparse after `a -> tau_A`?

## Computed answer

No. At `N=200000`, on three quadratic slopes and their convergent denominators:

- the input mismatch fraction falls to `1.2e-4`--`2.1e-4` on the deepest
  golden/square-root rows;
- the transformed mismatch fraction remains between roughly `0.84` and `0.95`;
- the mean absolute transformed defect remains order one (`3.6`--`8.4` in the
  representative deep rows), rather than becoming sparse;
- matched-density random controls occupy the same dense-output regime.

The receipt stores every denominator, count, mismatch fraction, integer
`L1` defect and random control. Sturmian bits were generated at 80-decimal
precision; the receipt records the minimum distance of every tested `n*alpha`
from an integer, which is vastly above the rounding scale.

This is not the vague statement that the divisor transform loses information:
it is exactly invertible by Möbius inversion. It loses the **additive locality**
that the Hecke–Mahler sparse-defect proof consumes. A convergent shift that is
almost a period of `a` is not remotely an almost-period of `tau_A`.

## Mechanism decision

The direct transfer

    sparse Sturmian convergent shifts -> sparse Lambert-coefficient shifts

is eliminated. Applying the Hecke–Mahler theorem separately to
`H_A(1/2), H_A(1/4), ...` also does not settle their infinite sum.

A Sturmian route remains open only if it controls the whole tower in (1), for
example by an algebraic-independence theorem compatible with the dependent
points `2^-r`, or by a nonlocal functional that survives divisor convolution.
No such input is supplied here, and no irrationality claim for the Sturmian
Lambert value is made.
