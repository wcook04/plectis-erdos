# The phase-numerator valuation does not strengthen the \(1/465\) gate

This note concerns the phase numerator in
`AnchorFourFiveFixedHorizonReduction.md`.  For a selected prefix
\(F_d\subseteq\{1,\ldots,d\}\), that note defines odd \(P_d\), an integer
\(N_d\), the diagonal remainder \(\rho_d\), and an integer \(B_d\) satisfying

\[
 465P_d\rho_d=4^dN_d-B_d.                         \tag{1}
\]

The consequence \(v_2(B_d)=d\) at a gate \(\rho_d=2^d\) is correct, but it
does not impose an additional whole-prefix restriction.

## 1. Exact valuation collapse

Suppose \(\rho_d\ne0\) and \(v_2(\rho_d)<2d\).  Rearranging (1) gives

\[
 B_d=4^dN_d-465P_d\rho_d.                        \tag{2}
\]

The first term on the right has 2-adic valuation at least \(2d\), whereas
the second has valuation exactly \(v_2(\rho_d)\), since both \(465\) and
\(P_d\) are odd.  The valuations are unequal, so

\[
 \boxed{v_2(B_d)=v_2(\rho_d).}                   \tag{3}
\]

In particular, at \(\rho_d=2^d\), equation (3) reads
\(v_2(B_d)=d\).  This is a consequence of the gate value itself, not a new
condition on the selected prefix.  The congruence one step beyond the
valuation also collapses:

\[
 \boxed{\frac{B_d}{2^dP_d}\equiv-465\pmod {2^d}}
                                                               \tag{4}
\]

at every gate.  Indeed, divide (2) by \(2^dP_d\); the first term is zero
modulo \(2^d\), and the second is \(-465\).

The valuation is not sufficient to recognize a gate, even for the fixed
target \(1/465\).  At \(d=9\), take the nongreedy prefix

\[
 F_9=\{2,3,4,6,7\}.
\]

Direct quotient arithmetic gives

\[
 \rho_9=\left\lfloor\frac{4^9}{465}\right\rfloor
 -\sum_{a\in F_9}\left\lfloor\frac{4^9}{2^a-1}\right\rfloor
 =-147968=-289\cdot2^9.
\]

Thus \(v_2(B_9)=v_2(\rho_9)=9\), although this prefix is not a gate.  This
example is only a falsifier for sufficiency of the valuation; it is not the
actual diagonal word.

## 2. Isolated odd-prime reductions are also automatic

There is a similarly limited obstruction to using one primitive prime at a
time.  Suppose an odd prime \(p\nmid465\) divides exactly one selected
denominator \(2^a-1\).  Put \(E=P_d/(2^a-1)\), so \(p\nmid E\).  Reduction of
the definition of \(B_d\) modulo \(p\) leaves only the \(a\)-term:

\[
 B_d\equiv-465r_{a,d}E\pmod p.                   \tag{5}
\]

Likewise \(N_d\equiv-465E\pmod p\).  The proposed gate right-hand side
therefore satisfies

\[
 2^d(2^dN_d-465P_d)
 \equiv-465\,4^dE
 \equiv-465r_{a,d}E
 \pmod p.                                        \tag{6}
\]

Thus the gate congruence at such a prime is automatic, whether or not the
prefix is a gate.  This does not eliminate odd-prime arguments involving
shared factors, several denominators at once, or size.  It only shows that an
isolated primitive-prime reduction of the displayed phase identity cannot
give the missing contradiction.

## 3. The surviving 2-adic condition is a long divisor-pulse carry

For \(j\ge2\), write

\[
 h_j=u_j-A_j-b_j.
\]

The diagonal recurrence can be written

\[
 \rho_j=4\rho_{j-1}+h_j-b_j2^j.                  \tag{7}
\]

After iteration, every term \(b_j2^j4^{d-j}\) is divisible by \(2^d\).
The terms \(4^{d-j}h_j\) with \(j\le\lfloor d/2\rfloor\) are also divisible
by \(2^d\).  Hence

\[
 \boxed{
 \rho_d\equiv
 \sum_{j=\lfloor d/2\rfloor+1}^{d}4^{d-j}h_j
 \pmod {2^d}.}                                   \tag{8}
\]

For even \(d=2m\), divisibility by \(2^d=4^m\) is equivalently the following
carry chain.  Starting with \(c_0=0\), all \(m\) integers

\[
 c_{i+1}=\frac{h_{d-i}+c_i}{4},
 \qquad 0\le i<m,                                \tag{9}
\]

must exist.  For odd \(d=2m+1\), the first \(m\) divisions in (9) must
exist and \(h_{d-m}+c_m\) must be even.

Thus a gate requires a carry chain of length about \(d/2\) whose digits are
the actual fixed-source/divisor-load pulses.  This is the genuine 2-adic
condition left after (3), but it is still only necessary: it proves
\(2^d\mid\rho_d\), not the Archimedean equality \(\rho_d=2^d\).  A closure
must couple (9) to the globally generated divisor loads and to the upper-strip
and next-pulse conditions.  Repackaging the same condition as
\(v_2(B_d)=d\) cannot supply that coupling.

There is an exact recut form which also retains the binary suffix capacity.
Put \(\ell=\lceil d/2\rceil\) and \(q=d-\ell\).  Iterating (7) from
\(\ell\) to \(d\), dividing by \(4^q\), and imposing the gate
\(\rho_d=2^d\) gives

\[
 \boxed{
 \rho_\ell
 =2^{\,2\ell-d}
 +\sum_{j=\ell+1}^{d}b_j2^{\,2\ell-j}
 +\sum_{j=\ell+1}^{d}
   \frac{A_j+b_j-u_j}{4^{j-\ell}}.}               \tag{10}
\]

The first sum after the leading term is the integer represented by the
selected binary suffix at this recut.  Consequently the final weighted
divisor-pulse correction in (10) must itself be an integer.  Equation (10),
unlike (3), couples the earlier remainder, binary suffix capacity, and all
divisor pulses across half of the prefix.  It is still an exact reformulation
of the gate, not its exclusion.  A useful next theorem would bound or classify
this correction using the actual divisor ancestry rather than treating its
digits independently.

The carry chain already rejects the synthetic \(24\to25\) phase/load
countermodel from the fixed-horizon note.  At its hypothetical skipped gate,
\(h_{24}=u_{24}-A_{24}=0\), so the first carry is \(c_1=0\).  The actual
prefix through rank 23 has \(u_{23}=0\), \(A_{23}=2\), and \(b_{23}=1\), hence
\(h_{23}=-3\).  The next numerator in (9) is therefore \(-3\), not a multiple
of four.  The synthetic value \(\rho_{23}=2^{22}\) used in that countermodel
cannot arise from this full pulse prefix.  This is a checked rejection of
that one countermodel, not an all-depth exclusion.

## 4. Boundary

Equation (3) removes the phase-numerator valuation as the proposed remaining
target.  It does not refute the exact identity (1), and it does not exclude
the fixed \(1/465\) gate.  Information beyond the 2-adic valuation must enter:
for example a multi-factor odd-prime restriction not already obtained by
reducing (1), an Archimedean bound strong enough to determine the multiple of
\(2^d\), or a theorem forbidding the length-\(\lfloor d/2\rfloor\) carry
chain (9), or equivalently the recut identity (10), for the actual divisor
loads.
