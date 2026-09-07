# Elementary domination of two advertised rationality constraints

Ordinary observations. They do not contradict the existing Lean statements
`exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction` or
`supportCoeffZeroWindow_length_le_eps_logb_add`. They do contradict the
live-paper habit of advertising those conclusions as arithmetic restrictions
on hypothetical rational counterexamples.

## Zero windows (every nonempty support)

If \(A\neq\varnothing\) and \(a_0=\min A\), every zero window of
\(c_A(n)=\#\{a\in A:a\mid n\}\) has length at most \(a_0-1\).

**Proof.** Every \(a_0\) consecutive integers contain a multiple of \(a_0\),
and \(c_A\) is at least \(1\) there. ∎

This proves the displayed sublogarithmic-window conclusion with a uniform
bound \(B=a_0-1\), with no rationality assumption, no divisor estimates, and
no \(\varepsilon\)-dependence. A support-independent bound would be false:
\(A=\{m\}\) has a zero window of length \(m-1\).

## Unbounded shifted tails (every infinite support)

For any infinite \(A\) and fixed integer \(c\ge0\), the sequence
\[
T_{c+N}=\sum_{r\ge1}c_A(c+N+r)\,2^{-r}
\]
is unbounded as \(N\to\infty\).

**Proof.** Choose any \(k\) distinct elements of \(A\), and let \(L\) be a
common multiple greater than \(c\). Then \(c_A(L)\ge k\), so
\(T_{L-1}\ge k/2\). Multiples of the same common multiple make these
examples arbitrarily late. ∎

Finite supports supply the contrast: \(A=\{2,3\}\) has a bounded periodic
tail. The genuinely arithmetic clauses in the rational-orbit theorems are
the integral lattice, the residue class, and the exact recurrence.
Unboundedness alone neither discriminates rational from irrational supports
nor rules out a candidate support.

The reconstruction script checks both statements on a small finite set. The
ordinary proofs above are the authority.
