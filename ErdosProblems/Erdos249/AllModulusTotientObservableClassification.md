# All-modulus rationality classification for totient observables

Ordinary proof.  Proposed statement: Type B revision packet
`erdos_revision_packets_r2_20260906`, file `05_questions_for_type_a.md`,
Theorem A.  Independently rewritten and checked here; not a Lean theorem.

Evidence class: `ordinary_proof`.  **Do not register as `lean_checked`.**

## Statement

Let \(m,b\ge 2\) and \(f:\mathbb Z/m\mathbb Z\to\mathbb Q\).  Write
\(R=\operatorname{rad}(m)\) and
\[
 T_{m,b}(f)=\sum_{n\ge 1}f(\varphi(n)\bmod m)\,b^{-n}.
\]
Let \(\mathcal R_m\) be the set of residue classes attained by \(\varphi(n)\)
for infinitely many \(n\).  The following are equivalent:

1. \(T_{m,b}(f)\) is rational.
2. The sequence \(n\mapsto f(\varphi(n)\bmod m)\) is eventually constant.
3. For every \(n\) that does **not divide** \(R\),
   \(f(\varphi(n)\bmod m)=f(0)\).
4. \(f\) is constant on \(\mathcal R_m\).

When these hold the constant is \(f(0)\) and
\[
 T_{m,b}(f)=\frac{f(0)}{b-1}
 +\sum_{d\mid R}\bigl(f(\varphi(d)\bmod m)-f(0)\bigr)b^{-d}.
\]
The rationality answer is independent of the base \(b\ge 2\).  Every residue
with only finitely many totient preimages has all of those preimages among
the divisors of \(R\).

## Hypotheses (explicit)

- Dirichlet's theorem on primes in reduced arithmetic progressions.
- Schur's polynomial-prime-divisor argument (a nonconstant integer
  polynomial takes values with infinitely many prime divisors).  Chebotarev
  is not used.
- The bounded-pulse irrationality criterion: a bounded integer coefficient
  sequence with arbitrarily long two-sided isolated nonzero digits has
  irrational base-\(b\) value.  Lean-checked at \(b=2\) as
  `irrational_dyadicValue_of_pulses` in `ResidueClassTotientSeries.lean`.
  The same tail argument works for every integer \(b\ge 3\) (ordinary).
- Isolation at **prime-power centres** \(n_0=ap^\nu\), not merely prime
  centres \(ap\).  Auxiliary primes solving \(ax^\nu\equiv t\pmod{\ell}\)
  with \(\ell\equiv 1\pmod m\) are produced by a primitive-element polynomial
  and Schur, then glued by CRT.
- Hensel unit replacement (Lemma A4): if \(p\mid m\) and \(\nu\ge 2\), some
  unit \(s\pmod m\) satisfies
  \(s^{\nu-1}(s-1)\equiv p^{\nu-1}(p-1)\pmod m\).  Ford–Konyagin–Pomerance
  Lemma 2 is the antecedent for primes \(\equiv 3\pmod 4\); the version used
  here covers \(p=2\) as well.  This is an arithmetic ingredient, not a
  series theorem.
- Ford–Konyagin–Pomerance totient-free classes \(302,790\bmod 1092\) are
  cited as an external arithmetic fact for the second negative result, not
  as a series theorem.

## Why this is not a live specialisation

`irrational_totientObservable` is a **sufficient** unit-centre criterion,
not an iff, and it fails at residue \(2\bmod 12\) because \(\gcd(3,12)=3\neq 1\).
The dyadic classification (rational iff constant on **even** residues at
\(m=2^k\)) is the case \(m=2^k\) of the present theorem, because there
\(\mathcal R_m\) is exactly the even residues.  The present theorem is not
the other way around: it is not a corollary of the dyadic statement, nor of
the Lean kernel-basis theorems (`totient_dyadic_odd_core_basis`,
`all_base_totient_kernel_rank_unconditional`).

## Proof sketch

Clear denominators of \(f\) and subtract \(f(0)\), obtaining an integer map
\(g\) with \(g(0)=0\).  Rationality of \(T_{m,b}(f)\) is equivalent to
rationality of \(T_{m,b}(g)\).  Isolation at centres \(ap^\nu\) with unit
\(s\) produces two-sided zero windows of arbitrary length around a letter
\(g(r)\), \(r\equiv\varphi(a)s^{\nu-1}(s-1)\pmod m\).  The bounded-pulse
criterion then forces \(g(r)=0\).

Take \(n\nmid R\).  Either some prime \(p\nmid m\) divides \(n\), or some
prime \(p\mid m\) divides \(n\) to exponent \(\nu\ge 2\).  Write \(n=ap^\nu\)
with \(p\nmid a\).  In the first case \(s=p\) is a unit modulo \(m\).  In
the second case Lemma A4 replaces the local factor by a unit \(s\).  In both
cases \(g(\varphi(n)\bmod m)=0\).  This is (1)\(\Rightarrow\)(3).

Condition (3) says the coefficients differ from \(f(0)\) only at the finitely
many indices dividing \(R\).  Summing those exceptions gives the displayed
formula, hence rationality and eventual constancy.  An eventually constant
rational sequence has a rational base-\(b\) series.  The eventual constant
must be \(f(0)\), because there are arbitrarily large primes
\(p\equiv 1\pmod m\) and then \(\varphi(p)\equiv 0\pmod m\).

Each residue arising from an index \(n\nmid R\) has infinitely many preimages
by the same representation and isolation.  Conversely an infinitely recurrent
residue has a preimage outside the finite set of divisors of \(R\).  Thus
\(\mathcal R_m=\{\varphi(n)\bmod m:n\nmid R\}\), which is also the set of
unit-centre residues after Lemma A4.  Residue \(0\) belongs to the set, so
(3) and (4) are equivalent with constant \(f(0)\).

The recurrent support is finite and computable: Carmichael \(\lambda\), the
unit semigroup \(H_m\), and the local factors \(E_p\) for \(p\mid m\) give
\(\mathcal R_m=H_m\prod_{p\mid m}E_p\).  Implementation:
`scripts/check_recurrent_totient_residues.py`.

## Negative results

**Prime centres miss a recurrent even residue.**  Residue \(2\bmod 12\) is
attained infinitely often, but never as \(\varphi(a)(s-1)\) with
\(\gcd(s,12)=1\).  For \(a\ge 3\), \(\varphi(a)\) is even and every unit
modulo \(12\) is odd, so the product is \(0\bmod 4\), while \(2\equiv 2\bmod 4\).
For \(a\le 2\), \(\varphi(a)\in\{0,1\}\) and the unit list
\(\{1,5,7,11\}\) yields residues \(0,4,6,10\).  Conversely, every prime
\(p\equiv 11\pmod{12}\) satisfies \(\varphi(p^2)=p(p-1)\equiv 2\pmod{12}\).
Witness: \(\varphi(121)=110\).  Lean:
`PrimeSquareResidueWitness.lean`
(`totient_oneTwoOne`, `no_unit_centre_two_mod_twelve`,
`two_mod_twelve_recurrent_via_prime_squares`).  Isolation of those squares
is not in Lean.

**Constancy on all even residues is false in general.**  Ford–Konyagin–
Pomerance exhibit totient-free classes \(302\) and \(790\) modulo \(1092\).
The indicator of residue \(302\) has identically zero series in every base,
yet is not constant on the even residues.  The finite formula independently
reproduces \(\lvert\mathcal R_{1092}\rvert=544=546-2\).

## Claim boundary

This theorem classifies **bounded** residue observables of \(\varphi\).  The
coefficients of \(S=\sum\varphi(n)2^{-n}\) are unbounded, so the theorem does
**not** imply \(S\notin\mathbb Q\) and does not close
`totient_specific_moving_dyadic_escape`.  The first-harmonic estimate remains
unproved.  Affine totient independence (Type B Lemma D) is not recorded here:
the live module `AllBaseTotientKernel.lean` already supplies an unconditional
Lean rank/basis by a finite-determinant argument, with Martin's density
theorem remaining prior art rather than a Lean dependency.
