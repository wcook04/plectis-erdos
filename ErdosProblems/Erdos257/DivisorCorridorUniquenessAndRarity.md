# Divisor-corridor uniqueness and the exact rarity law

Let
\[
 M_n=2^n-1,
 \qquad
 D=D_{H,r}=\prod_{\substack{d\mid H\\d\le r}}\Phi_d(2),
\]
where \(r,r-1\mid H\).  Then \(M_rM_{r-1}\mid D\), since consecutive
Mersenne numbers are coprime.  After removing the common cyclotomic factors
above \(r\), a divisor-only Boolean prefix \(F\) has the form
\[
 K_F=A-3\sum_{n\in F}\frac D{M_n},                \tag{1}
\]
and the moving fatal corridor is
\[
 I_r=\left[6\frac D{M_r},\,3\frac D{M_{r-1}}\right). \tag{2}
\]
Its exact integer width is
\[
 W_r=\frac{3D}{M_{r-1}M_r}.                       \tag{3}
\]

The results below explain rigorously why divisor-only corridor hits are so
rare.  They do not, by themselves, exclude the fixed incoming root charge
\(A=1510D/M_{15}\).

## 1. Reverse-superincreasing separation

For every \(j\ge1\),
\[
 \frac1{M_j}-\sum_{k=j+1}^{\infty}\frac1{M_k}
 >2^{-2j-1}.                                      \tag{4}
\]
Indeed,
\[
 \sum_{k=j+1}^{\infty}\frac1{2^k-1}
 <\frac{2^{-j}}{1-2^{-(j+1)}},
\]
whereas
\[
 \frac1{2^j-1}=\frac{2^{-j}}{1-2^{-j}}.
\]
Subtracting the two displayed bounds gives more than \(2^{-2j-1}\).

Let \(F\ne G\) be subsets of any eligible ranks below \(r\), and let \(j\)
be their smallest differing rank.  The term at \(j\) dominates every later
possible difference, so (4) gives, when \(j\le r-2\),
\[
 |K_F-K_G|
 >3D\,2^{-2j-1}
 \ge3D\,2^{-(2r-3)}
 >\frac{3D}{M_{r-1}M_r}=W_r.                      \tag{5}
\]
The last inequality uses
\(M_{r-1}M_r>2^{2r-3}\).  If \(j=r-1\), the difference is
\(3D/M_{r-1}>W_r\) directly.

Therefore
\[
 \boxed{\text{the fatal corridor contains at most one divisor-prefix
 Boolean coefficient }K_F.}                       \tag{6}
\]
This holds for every eligible subset of ranks below \(r\); sparsity of the
divisor set can only strengthen it.

## 2. Primitive coordinates make the charge code injective

Suppose all eligible ranks are at least \(7\).  This is automatic for a
positive state descended from the anchor-\(15\) root, because selecting any
rank \(n\le6\) subtracts
\(3/M_n>1510/M_{15}\) and makes the coefficient negative.

The map
\[
 F\longmapsto
 \sum_{n\in F}\frac D{M_n}\pmod D                \tag{7}
\]
is injective.  If two sets differed, let \(j\) be their largest differing
rank.  By Bang--Zsigmondy, \(M_j\) has a primitive prime divisor \(p_j\),
because \(j\ge7\).  Put \(e=v_{p_j}(D)\).  For every \(k<j\), the order
condition gives \(p_j\nmid M_k\), so \(D/M_k\) vanishes modulo \(p_j^e\).
All terms with \(k>j\) have zero difference by the choice of \(j\).  But the
remaining coefficient
\[
 \pm\frac D{M_j}
\]
has \(p_j\)-adic valuation \(e-v_{p_j}(M_j)<e\), and cannot vanish modulo
\(p_j^e\).  This contradiction proves injectivity.

Thus the nested primitive-charge vector is a lossless encoding of the
Boolean genealogy.  The repeated prime factors along order-\(p^a\) chains do
not create collisions: the full prime-power valuation in \(D\) separates
the highest differing rank.

## 3. Exact bad-translation density

Let \(E\subseteq\{7,\ldots,r-1\}\) be the eligible ranks and \(m=|E|\).
Regard the incoming affine charge \(A\) as a residue modulo \(D\).  For each
fixed \(F\subseteq E\), exactly \(W_r\) residues \(A\pmod D\) place (1) in
the residue interval (2).  Hence the union bound, together with (3), gives
\[
 \frac{\#\{A\pmod D:\exists F,\ K_F\in I_r\}}D
 \le \frac{2^mW_r}{D}
 =\frac{3\,2^m}{M_{r-1}M_r}.                      \tag{8}
\]
Since \(m\le r-7\),
\[
 \boxed{
 \frac{\#\text{ bad affine charges}}D
 <\frac3{2^{r+4}}.}                               \tag{9}
\]

Equations (6)--(9) are the sought joint binary/LCM law: primitive charges
retain the complete Boolean ancestry, reverse superincreasingness allows at
most one genealogy in a corridor, and the two adjacent Mersenne pulses make
the set of aligning incoming charges exponentially sparse.

The remaining obstruction is correspondingly precise.  The actual root
charge is one fixed, highly structured residue, not a uniformly varying
translation.  A complete divisor-only exclusion must prove that
\(1510D/M_{15}\) never belongs to the exceptional set counted in (8).

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/divisor_corridor_uniqueness_and_rarity.py

for exact separation, injectivity, and density receipts.
