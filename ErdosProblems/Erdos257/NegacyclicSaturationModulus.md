# The moving negacyclic modulus and its half-depth descent

For (R\geq2), put
\[
 M_R=2^R+1,
 \qquad
 q_R(d)=\left\lfloor\frac{2^{2R}}{2^d-1}\right\rfloor,
 \qquad
 Q_R=\left\lfloor\frac{2^{2R}}{21}\right\rfloor.
\]
This note applies the moving modulus (M_R) to the sparse saturation row
\[
 \sum_{d\in D}q_R(d)=Q_R-2^R.                     \tag{S}
\]
Unlike a fixed low-bit modulus, (M_R) retains the complete folded
(R)-bit quotient word.  It gives an exact pulse-discrepancy formula and an
exact descent to a denominator-21 row at half depth.  It does not by itself
close the sparse socket: divisors of (R) form an unbounded blind kernel
which survives the endpoint-pulse constraint.  The full primitive
prime-power charges remove that kernel as an information loss, but not as an
existence obstruction: they encode the blind Boolean subset injectively and
leave the same exact achievement test.

## 1. Lower-half minus folded-upper-half pulses

The quotient has the finite geometric expansion
\[
 q_R(d)=\sum_{j=1}^{\lfloor2R/d\rfloor}2^{2R-jd}.  \tag{1}
\]
Modulo (M_R), powers at height at least (R) fold with a minus sign.
Consequently
\[
 q_R(d)\equiv
 \sum_{R<jd\leq2R}2^{2R-jd}
 -\sum_{jd\leq R}2^{R-jd}pmod {M_R}.              \tag{2}
\]

Write (R=hd+r), (0\leq r<d), and put
\[
 A_{R,d}=\sum_{j=1}^h2^{R-jd},
 \qquad
 \epsilon_{R,d}=\mathbf1_{2r\geq d}.
\]
Pairing the two halves of (2) gives the canonical nonnegative residue
\[
 \boxed{
 \delta_R(d)
 =(2^r-1)A_{R,d}
 +\epsilon_{R,d}2^{2r-d}.}                        \tag{3}
\]
It satisfies
\[
 0\leq\delta_R(d)<2^R<M_R,
 \qquad q_R(d)\bmod M_R=\delta_R(d).              \tag{4}
\]
For example, the first term in (3) is a disjoint union of (h) binary
blocks of (r) ones, separated by gaps of length (d-r); the optional
last term is the unpaired endpoint pulse.

In particular,
\[
 \boxed{\delta_R(d)=0\iff d\mid R.}               \tag{5}
\]
This is the exact moving-modulus version of the lower/upper pulse
cancellation suggested by the numerics.

## 2. Exact quotient, not just congruence

There is a stronger identity.  Define the half-depth quotient
\[
 \widehat q_R(d)=\left\lfloor\frac{2^R}{2^d-1}\right\rfloor.
\]
Then
\[
 \boxed{
 q_R(d)=M_R\widehat q_R(d)+\delta_R(d).}           \tag{6}
\]
To prove it, write (2^R=a(2^d-1)+b).  Squaring and dividing by
(2^d-1) shows that the quotient by (M_R) is exactly (a); the remainder
is (3).  When (d\mid R), (6) becomes
\[
 q_R(d)=M_R\frac{2^R-1}{2^d-1}.                   \tag{7}
\]
Thus the terms invisible modulo (M_R) are not lost: they become exact
half-depth geometric coins.

## 3. The target residue for (R\equiv2\pmod3)

Put
\[
 \widehat Q_R=\left\lfloor\frac{2^R}{21}\right\rfloor,
 \qquad b_R=2^R\bmod21.
\]
For (R\equiv2\pmod3), one has (b_R=4) when (R\equiv2\pmod6), and
(b_R=11) when (R\equiv5\pmod6).  The same squaring calculation gives
\[
 Q_R-2^R=M_R(\widehat Q_R-1)+a_R,                 \tag{8}
\]
where
\[
 a_R=
 \begin{cases}
 \displaystyle\frac{M_R+2}{7},&R\equiv2\pmod6,\\[2mm]
 \displaystyle\frac{10M_R+6}{21},&R\equiv5\pmod6.
 \end{cases}                                      \tag{9}
\]
Both representatives lie in ([0,M_R)).  In the even case, 21 is
invertible modulo (M_R), and the first formula is the unique reduced
target residue.

The winding in (8) is itself the half-depth denominator-21 target:
\[
 \widehat Q_R-1=
 \begin{cases}
 (2^R-25)/21,&R\equiv2\pmod6,\\
 (2^R-32)/21,&R\equiv5\pmod6.
 \end{cases}                                      \tag{10}
\]

## 4. Quotienting out the blind divisor sublattice

Split a candidate support as
\[
 D=V\mathbin{\dot\cup}E,
 \qquad
 E=\{d\in D:d\mid R\},
 \qquad
 V=D\setminus E.
\]
For the visible part, define its negacyclic winding (k) by
\[
 \sum_{d\in V}\delta_R(d)=a_R+kM_R.              \tag{11}
\]
Using (6)--(8), the full saturation equation (S) is equivalent to the pair
\[
 \boxed{
 \begin{aligned}
 \sum_{d\in V}\delta_R(d)&=a_R+kM_R,\\
 \sum_{d\in V}\widehat q_R(d)
 +\sum_{d\in E}\frac{2^R-1}{2^d-1}
 &=\widehat Q_R-1-k.
 \end{aligned}}                                   \tag{12}
\]
This is the exact reduced visible subset-sum equation.  A congruence
solution is only the first line; the divisor terms must solve the remaining
half-depth deficit in the second line.

The coin with (d=R) is one, while every proper divisor contributes a
geometric repunit.  Thus the blind terms can change the winding equation,
but only through the Boolean achievement set
\[
 \left\{
 \sum_{d\in E}\frac{2^R-1}{2^d-1}:E\subseteq\{d:d\mid R,\ d\geq2\}
 \right\}.                                        \tag{13}
\]
They are not an arbitrary scalar correction.

There is a useful scale bound on the descent.  Every visible residue lies
strictly between zero and (M_R).  Since (0<a_R<M_R), the first line of
(12) forces
\[
 0\leq k\leq |V|-1\leq R-2.                       \tag{14}
\]
Consequently every saturation solution would produce the half-depth row
\[
 \boxed{
 \sum_{d\in D}\left\lfloor\frac{2^R}{2^d-1}\right\rfloor
 =\left\lfloor\frac{2^R}{21}\right\rfloor-e,
 \qquad 1\leq e=1+k\leq R-1.}                    \tag{15}
\]
Thus the residual is only linear while the row itself has exponential
scale.  For (R\geq8), the terms (d=2,3,4) each exceed the target on the
right and are automatically absent.  A moving saturated row must therefore
descend to a near-exact denominator-21 achievement row supported on
(d\geq5), with the original endpoint-pulse restrictions still attached.

## 5. A scalable blindness theorem

The sparse pulse in (S) is
\[
 p_R=2\#\{d\in D:d\mid2R+1\}
 +\#\{d\in D:d\mid2R+2\}.
\]
If (d\mid R) and (d>2), then (d) divides neither endpoint.  Hence
\[
 \delta_R(d)=0,
 \qquad
 \text{the contribution of }d\text{ to }p_R=0.    \tag{16}
\]
For the next endpoint pair (2R+3,2R+4), the same conclusion holds for
every (d\mid R) with (d>4).

Therefore the moving negacyclic residue together with either sparse pulse
still cannot recover the divisor sublattice.  Every subset of the eligible
divisors may be toggled without changing those observed coordinates.  This
is an unbounded exact kernel, not a fixed-low-bit artefact.

Equation (12) is the minimal repair: retain the half-depth achievement
coordinate instead of discarding the winding.  It also states the remaining
problem without disguise.  One must prove that no visible solution of the
first line has a blind-divisor achievement equal to the exact deficit in the
second.  The negacyclic modulus has converted the high-window question into
a recursive denominator-21 row with a (-1-k) correction; it has not yet
proved that row impossible.

## 6. Primitive prime-power encoding of the blind set

Put (P_R=2^R-1), and let (p_f) be a primitive prime divisor of
(2^f-1), where (f\mid R).  Write

\[
 A_f=v_{p_f}(P_R).
\]

For a blind coin (L_d(R)=P_R/(2^d-1)), with (d\mid R), the order
condition and LTE give

\[
 v_{p_f}(L_d(R))=
 \begin{cases}
 A_f,&f\nmid d,\\
 v_{p_f}(R/d),&f\mid d.
 \end{cases}                                      \tag{17}
\]

Thus, after the visible support and winding have been fixed, the descended
equation (12) has the exact primitive charge rows

\[
 \boxed{
 \sum_{\substack{d\in E\\f\mid d}}L_d(R)
 \equiv
 \widehat Q_R-1-k-
 \sum_{d\in V}\widehat q_R(d)
 \pmod {p_f^{A_f}}.}                              \tag{18}
\]

The full exponent (A_f) matters.  Reduction only modulo (p_f) can have a
false kernel.  For example, take (R=155t).  Then (L_5(R)) vanishes modulo
(31), because (R/5=31t), but

\[
 v_{31}(L_5(R))=v_{31}(R/5)=1+v_{31}(t)
 < A_5=2+v_{31}(t),                               \tag{19}
\]

so the same coin is nonzero modulo (31^{A_5}).  The apparent infinite
modulo-31 toggle therefore only moves one layer upward; it is not in the
prime-power kernel.

In fact the rows (18) encode every blind subset of eligible ranks (d\geq5)
injectively.  If two subsets differ, take their largest differing rank (j).
For (j\ne6), choose a primitive prime of (2^j-1).  All lower-rank difference
terms vanish modulo its full power in (P_R), while (L_j(R)) does not.  For
the Zsigmondy exception (j=6), the prime (7), of order (3), does the same
job: the only lower eligible rank is (5), and (3\nmid5).  Hence the two
charge vectors cannot agree.

Thus the full charge vector determines the blind subset.  Once (V) and (k)
are fixed, however, (18) is equivalent to the Boolean achievement question
in the second line of (12).  It supplies no sign forcing the encoded subset
to meet either endpoint pair.

There is an exact reduced-socket counterexample to any claim that the small
remainder, both sparse pulses, and all primitive charge rows alone are
inconsistent.  At (R=140), descending integer greedy on the coins
(\widehat q_{140}(d)), (5\leq d\leq140), gives the support

\[
\begin{split}
G=\bigl\{&5,7,8,9,10,11,13,16,18,20,22,24,28,32,34,37,39,42,45,46,47,\\
&49,50,51,53,54,57,58,59,60,61,67,71,73,77,78,79,82,83,84,86,\\
&91,93,105,107,109,111,115,117,118,119,123,124,131,132,133,134,\\
&139,140\bigr\}.
\end{split}
\]

It satisfies

\[
 \sum_{d\in G}\widehat q_{140}(d)=\widehat Q_{140}.
\]

Since (\widehat q_{140}(140)=1), the set (G'=G\setminus\{140\})
therefore realizes (e=1) in (15).  Moreover its two consecutive endpoint
pulses are both one:

\[
 2\#\{d\in G':d\mid281\}+\#\{d\in G':d\mid282\}=1
\]

from (d=47), and

\[
 2\#\{d\in G':d\mid283\}+\#\{d\in G':d\mid284\}=1
\]

from (d=71).  Because the descended equality is exact, it satisfies every
prime-power congruence obtained from that equality, including (18).  Its
blind subset is (\{5,7,10,20,28\}), which the charge vector recovers without
forcing a pulse.

This example is deliberately classified.  It does **not** satisfy the first,
visible negacyclic equation in (12), so it is not a solution of (S).  It
shows instead that the first equation cannot be discarded: prime-power
recovery, the bound (1\leq e\leq R-1), and the two sparse-pulse bounds are
jointly consistent.  The additional statement required for exclusion is the
following implication.  If (V) satisfies (11), and the charge vector decodes
an (E) which satisfies the second line of (12), then

\[
 p_R(V\cup E)\geq2
 \quad\hbox{or}\quad
 p_{R+1}(V\cup E)\geq2.                           \tag{20}
\]

This implication couples the folded visible word to the recovered divisor
subset.  Neither coordinate separately implies it.

## 7. Equal-leading-position cohorts rule out a bounded-window proof

For a visible rank (d), write

\[
 R=hd+r,\qquad t=d-r.
\]

Then (1\leq t<d), (d\mid R+t), and the highest nonzero bit of
(\delta_R(d)) is at exponent (R-t-1).  Equivalently,

\[
 2^{R-t-1}\leq\delta_R(d)<2^{R-t}.                \tag{21}
\]

Indeed, the product in (3) consists of disjoint blocks of (r) ones,
separated by gaps of length (t).  Thus all ranks in the same (t)-cohort
have the same leading position.  The endpoint conditions become

\[
\begin{array}{c|c}
d\mid2R+1&2t\equiv1\pmod d\\
d\mid2R+2&2t\equiv2\pmod d\\
d\mid2R+3&2t\equiv3\pmod d\\
d\mid2R+4&2t\equiv4\pmod d.
\end{array}                                      \tag{22}
\]

Consequently (p_R\leq1) excludes the first class and permits at most one
rank in the second; (p_{R+1}\leq1) has the analogous effect on the third
and fourth classes.

These facts do not give a superincreasing order by leading position.  The
failure persists at arbitrarily large heights and widths.  Fix
(U\geq6) with (3\mid U), put

\[
 A=\left\lfloor\frac{2^U}{7}\right\rfloor
   =\frac{2^U-1}{7},
 \qquad N=\frac{A+1}{2},
 \qquad t=U-1.                                   \tag{23}
\]

Choose distinct odd primes (d_1,\ldots,d_N), all greater than (2t), so
large that

\[
 \sum_{i=1}^N2^{U-d_i}<1.                        \tag{24}
\]

The Chinese remainder theorem gives arbitrarily large (R) such that

\[
 R\equiv2\pmod6,
 \qquad R\equiv-t\pmod {d_i}\quad(1\leq i\leq N).
                                                               \tag{25}
\]

Every (d_i) is visible and belongs to the same (t)-cohort.  It contributes
to none of the four endpoint classes in (22), since
(4<2t<d_i).  Put (B=2^{R-U}).  The block description of (\delta) gives

\[
 \delta_R(d_i)=2B-D_i,
 \qquad 0<D_i<2^{R-d_i}.                         \tag{26}
\]

By (24), (0<\sum_iD_i<B), and hence

\[
 \left\lfloor
 \frac{\sum_i\delta_R(d_i)}B
 \right\rfloor
 =2N-1=A
 =\left\lfloor\frac{a_R}{B}\right\rfloor.       \tag{27}
\]

Thus the selected residues have exactly the same leading (U) bits as the
target while both endpoint pulses vanish.  Since (U) can be arbitrarily
large, no argument using a fixed number of leading bits, even together with
the two sparse-pulse conditions, can prove (20).  A successful carry
argument must use a window whose width grows with (R), or an equivalent
global constraint on the lower deficits (D_i).  Equation (27) does not give
the full congruence modulo (M_R); it isolates the information lost by
bounded leading-window arguments.

## 8. The lower carry forbids exact closure of one cohort

The preceding construction cannot be extended to an exact congruence while
retaining a single (t)-cohort.  Suppose

\[
 R\equiv2\pmod6,\qquad t\equiv2\pmod3,\qquad
 R\geq5t+20,                                      \tag{28}
\]

and let (E) be a set of visible ranks such that every (d\in E) satisfies
(d\mid R+t) and (d>t).  Put (C=2^{R-t}) and
(D_d=C-\delta_R(d)).  From the disjoint block formula,

\[
 0<D_d<2^{R-d}.                                   \tag{29}
\]

If (\sum_{d\in E}\delta_R(d)=a_R), then (29) first determines the
cardinality of (E), and gives

\[
 \boxed{\sum_{d\in E}D_d=\frac{3(C-1)}7.}         \tag{30}
\]

Indeed, (\sum_{d>t}2^{R-d}<C), so
(|E|=\lceil a_R/C\rceil=(2^t+3)/7).  Substitution gives (30).

The deficits retain the complete Mersenne denominator.  Direct
multiplication by (2^d-1) gives

\[
 D_d(2^d-1)=
 \begin{cases}
 C(2^t-1)+2^{d-t}(2^{d-t}-1),&d<2t,\\
 (2^t-1)(C-2^{d-2t}),&d\geq2t.
 \end{cases}                                      \tag{31}
\]

After division by (C(2^t-1)), equation (30) is an
(O(2^{-R})) perturbation of

\[
 \sum_{d\in E}\frac1{2^d-1}
 =\frac3{7(2^t-1)}.                               \tag{32}
\]

The first (t-1) greedy decisions in (32) can be computed uniformly.  Scale
by (2^t-1), put (z=2^{-t}), and write

\[
 b_s=\frac{2^t-1}{2^{t+s}-1}\qquad(s\geq1).
\]

Relative to the binary weight (2^{-s}), the reduction is

\[
 e_s=2^{-s}-b_s
 =\frac{z2^{-s}(1-2^{-s})}{1-z2^{-s}}.            \tag{33}
\]

The binary expansion of (3/7) selects offsets congruent to (2) or (0)
modulo (3).  These selected decisions remain selected after the reductions
(e_s).  A skipped offset (s\equiv1\pmod3) with (s\leq t-4) remains skipped,
because

\[
 \sum_{u\geq2}e_u
 <\frac{z}{2(1-z/4)}
 <\frac{16z}{7}
 \leq\frac{2^{-s}}7.                              \tag{34}
\]

At the final normally skipped offset (s=t-1), the inequality reverses:

\[
 e_2+e_3
 >\left(\frac3{16}+\frac7{64}\right)z
 =\frac{19}{64}z
 >\frac27z
 =\frac{2^{-(t-1)}}7.                             \tag{35}
\]

Thus the greedy support of (32) contains the three consecutive ranks

\[
 2t-3,\qquad2t-2,\qquad2t-1.                       \tag{36}
\]

This prefix is stable under the perturbation in (31).  The
reverse-superincreasing estimate

\[
 \frac1{2^j-1}-\sum_{n>j}\frac1{2^n-1}
 >2^{-2j-1}                                       \tag{37}
\]

after multiplication by (2^t-1), separates two subsets whose first
difference is at most (2t-1) by more than (2^{-3t}).  On the other hand,
(31) gives the explicit perturbation bound

\[
 \left|
 (2^t-1)\sum_{d\in E}\frac1{2^d-1}-\frac37
 \right|
 <\frac{3+R2^{1-t}}C
 <2^{-3t},                                        \tag{38}
\]

where the last inequality follows from (28).

Hence any subset satisfying (30) must contain the ranks in (36).  If one
of them is absent from the divisor cohort, (30) has no solution.  If
(2t-1) is present, then

\[
 R\equiv-t\pmod {2t-1}\quad\Longrightarrow\quad
 2t-1\mid2R+1.
\]

Its contribution to (p_R) is two.  We have proved

\[
 \boxed{
 \text{an exact single-}(t)\text{-cohort solution of }
 \sum\delta_R(d)=a_R\text{ cannot satisfy }p_R\leq1.}          \tag{39}
\]

The restriction to one (t)-cohort is essential.  Residues with larger (t)
change the right side of (30), while residues with smaller (t) change both
its scale and its cardinality term.  Extending (39) requires controlling
those cross-cohort contributions in the normalized deficit equation; the
fixed-window data excluded by (27) cannot do so.

## 9. Common-height arithmetic makes the safe migration graph contract

The apparent cross-cohort escape from (39) disappears if one retains the
parity of the cohort label.  This is an exact arithmetic effect, not a
numerical spectral observation.

Write (q=t\bmod 6).  The three forced endpoint labels in the ideal target
complement row depend on (p=t\bmod3):

\[
 J_0=\{1,2,4\},\qquad
 J_1=\{1,3,4\},\qquad
 J_2=\{1,2,3\}.                                  \tag{40}
\]

A label ((t,j)) has valuation (v=t-j).  Its valuation-preserving migration
to a safe label (j'\geq5) lies in the cohort and rank

\[
 u=t-j+j',\qquad d=2u-j'=2t-2j+j',               \tag{41}
\]

and carries relative dyadic mass (2^{j-j'}).  The rank belongs to a common
height (R) precisely when

\[
 R\equiv-u\pmod d.                               \tag{42}
\]

Because the saturation row has (R\equiv2\pmod6), (42) is compatible with
the target phase only if

\[
 \gcd(d,6)\mid u+2.                              \tag{43}
\]

This parity/gcd condition was invisible after quotienting the cohort state
modulo (3).  It is already strong enough to forbid additive recycling.
Let (A_{qr}) be the sum of (2^{j-j'}) over every edge satisfying
(40)--(43), where the source phase is (q), the destination phase is
(r=u\bmod6), and (j'\geq5).  Summing each residue class of (j') as a
geometric series of ratio (2^{-6}) gives

\[
A=
\begin{pmatrix}
1/21&65/126&65/252&16/63&4/21&2/63\\
2/63&2/63&65/126&16/63&43/168&4/63\\
8/63&2/63&2/63&0&11/42&8/63\\
43/168&4/63&4/63&1/63&11/21&1/252\\
16/63&8/63&8/63&0&1/21&32/63\\
1/63&65/252&16/63&8/63&2/21&1/63
\end{pmatrix}.                                   \tag{44}
\]

This matrix is an over-approximation: it retains two edges even when they
produce the same rank with incompatible cohort congruences.  Therefore a
contraction for (A) applies a fortiori to every edge family realizable at
one common (R).

For the positive phase weight

\[
 w=(100,78,47,80,78,55)^{\mathsf T},             \tag{45}
\]

direct multiplication gives

\[
 Aw\leq\frac{19}{20}w,                           \tag{46}
\]

with coordinate slacks

\[
 \left(
 \frac{241}{252},\frac{541}{1260},\frac{719}{1260},
 \frac{31}{252},\frac{743}{630},\frac{37}{252}
 \right).                                       \tag{47}
\]

Consequently every generation of a common-height, valuation-preserving,
all-safe migration forest loses at least (1/20) of its (w)-weighted
capacity.  No nonzero population can be covered componentwise by its safe
children.  In particular, the previously supercritical three-phase
truncation with (j'\in\{5,6,7\}) and its proposed 22-token recycling
multiset do not lift to one arithmetic height: every split of a
three-phase population into its two parity classes is subject to (46).

This settles the recycling question, but not mixed-cohort saturation.  To
apply (46) globally one must still prove a propagation statement: absent
an endpoint pulse, each forced target pivot in (40) must be assigned to a
valuation-preserving safe descendant without duplication or cancellation
through the lower-carry equation.  Equations (40)--(47) show that an
infinite all-safe descendant forest is impossible once that assignment is
available; they do not manufacture the assignment.

## 10. Lower-valuation carry defeats atomwise propagation

The missing assignment in the preceding paragraph cannot require an
individual descendant of the same valuation.  There is an exact
common-height counterexample.

Take (R=44).  The source label ((t,j)=(8,3)) has valuation (v=5), and its
short rank is (d_0=13).  Since (13\mid2R+3), this is a forbidden endpoint
atom.  Its exact deficit is

\[
 D_{44,13}=2,139,356,192\equiv32\pmod {64},
 \qquad v_2(D_{44,13})=5.                         \tag{48}
\]

On the other hand, ranks (12) and (28) are individually absent from all
four endpoint divisor classes.  They lie in cohorts (4) and (12), and

\[
\begin{aligned}
 D_{44,12}&=4,027,515,120\equiv48\pmod {64},\\
 D_{44,28}&=65,520\equiv48\pmod {64}.
\end{aligned}                                    \tag{49}
\]

Both deficits have valuation (4), but

\[
 D_{44,12}+D_{44,28}
 =4,027,580,640\equiv32\pmod {64},
 \qquad v_2(D_{44,12}+D_{44,28})=5.              \tag{50}
\]

Thus two safe lower-valuation atoms reproduce the complete six-bit state
of the forbidden pivot.  This is precisely the binary-carry operation
which is not represented by the valuation-preserving matrix (44).

The carry also survives a substantially longer exact target prefix.  Put

\[
 S=\{8,9,12,17,21,25,28,35,37\}.
\]

Every member of (S) is individually allowed by the two sparse endpoint
bounds, their total pulse pair is ((1,0)), and exact integer evaluation
gives

\[
 \sum_{d\in S}\delta_{44}(d)
 \equiv a_{44}\pmod {2^{17}}.                    \tag{51}
\]

This does not solve the full congruence modulo (2^{44}+1).  It does prove
that the required propagation theorem cannot follow from an atomwise
same-valuation rule, nor from a bounded low-prefix rule of the displayed
depth.  A valid propagation law must attach state to laminar carry ancestry
and control the odd units retained after pairing and division by two.  The
strict phase contraction (46) can close the argument only after such carry
nodes are shown not to duplicate or increase the phase-weighted inventory.

## 11. Arbitrarily deep carry impostors

The obstruction in Section 10 is not bounded-depth noise.  The deficits
have an exact Boolean block form.  Write (R=hd+r) and (t=d-r).  Directly
from (31), or by subtraction in the block formula (3), one obtains

\[
D_{R,d}=
\begin{cases}
\displaystyle
2^r+(2^t-1)\sum_{i=0}^{h-2}2^{2r+id},&r<t,\\[3mm]
\displaystyle
(2^t-1)\sum_{i=0}^{h-1}2^{r-t+id},&r\geq t.
\end{cases}                                      \tag{52}
\]

The displayed blocks are disjoint.  In particular,

\[
s_2(D_{R,d})=
\begin{cases}
(h-1)t+1,&r<t,\\
ht,&r\geq t,
\end{cases}                                      \tag{53}
\]

where (s_2) is binary popcount.  Formula (52) also produces an infinite
family of safe carries which mimic a forbidden pivot to unbounded 2-adic
depth.

Let (t\equiv0\pmod6), (t\geq6), and put

\[
 R=7t-4,qquad
 d_0=2t-1,qquad d_1=3t-1,qquad d_2=6t-2.       \tag{54}
\]

The source (d_0) has cohort (t), label (j=1), and valuation (t-1).
Moreover (d_0\mid2R+1), so it is forbidden by (p_R\leq1).  The provider
ranks have cohorts

\[
 u_1=2t+1,qquad u_2=5t,                         \tag{55}
\]

and both have valuation (t-2).  Neither provider divides any of
(2R+1,\ldots,2R+4): after subtracting (4d_1), respectively (2d_2), the
four remainders are (2t-3,2t-2,2t-1,2t), all strictly between zero and
the corresponding divisor.

Formula (52) gives the three deficits exactly:

\[
\begin{aligned}
D_0&=2^{t-1}+(2^t-1)
       \left(2^{2t-2}+2^{4t-3}\right),\\
D_1&=2^{t-2}+2^{2t-4}(2^{2t+1}-1),\\
D_2&=2^{t-2}.
\end{aligned}                                    \tag{56}
\]

Their mismatch is

\[
D_1+D_2-D_0
=2^{2t-4}
 \left(2^{2t+2}-2^{3t+1}-2^{t+2}+3\right).      \tag{57}
\]

The parenthesis is odd, and hence

\[
 \boxed{v_2(D_1+D_2-D_0)=2t-4.}                 \tag{58}
\]

After division by the common source factor (2^{t-1}), the safe carry pair
and forbidden source agree in their first (t-3) binary unit digits.  This
agreement depth is unbounded.  The smallest member is

\[
 (t,R;d_0,d_1,d_2)=(6,38;11,17,34),             \tag{59}
\]

which agrees for three normalized unit digits.  The next member
((12,80;23,35,70)) agrees for nine.

There is a sharper four-atom recut.  Add the two safe ranks

\[
 d_B=4t-2,qquad d_3=5t.                         \tag{60}
\]

Their cohorts are (t) and (3t+4), and (52) gives

\[
 D_B=2^{2t-2}(2^t-1),qquad D_3=2^{2t-4}.        \tag{61}
\]

Substitution in (57) cancels every lower discrepancy and yields the exact
identity

\[
 \boxed{
 D_1+D_B+D_3+D_2
 =D_0-2^{4t-2}(2^{t-1}-1).}                     \tag{62}
\]

Thus four safe atoms reproduce the forbidden deficit up to a single block
of (t-1) ones beginning at valuation (4t-2).  Their normalized agreement
depth is (3t-1), three times the source scale up to an additive constant.
The exposed valuation is already beyond the single-atom zone.  A short
atom of valuation (4t-2) would have rank greater than (8t-4>R).  A long
atom has rank greater than its valuation and hence greater than (R/2), so
its height count is one; solving its valuation equation gives
((10t-6)/3<4t-2), a contradiction.  Therefore no individual deficit at
height (R) begins at the first unmatched bit of (62).

The residual block can still, in principle, be synthesized by carries from
lower valuations.  Proving that it cannot is the exact anti-compression
problem left by this family.  At the smallest instance (t=6,R=38), an
exhaustive audit of all (2^{22}) subsets of individually endpoint-safe
ranks finds that the four ranks (\{17,22,30,34\}) attain the maximal
agreement valuation (22=4t-2).  This finite extremality is evidence for,
not a proof of, the uniform anti-compression statement.

There is, however, a uniform anti-compression theorem for forward ranks.
Formula (52) shows for every visible (d) that

\[
 D_{R,d}\leq2^{R-d}.                             \tag{63}
\]

Hence the total dyadic upper capacity strictly after the forbidden source
(d_0=2t-1) is

\[
 U=\sum_{d=2t}^{R}2^{R-d}=2^{5t-3}-1.           \tag{64}
\]

This estimate has a large forced loss at one arithmetically specified
rank.  Put

\[
 d_*=(R+1)/3=(7t-3)/3.                           \tag{65}
\]

It is an integer because (6\mid t), and (R=3d_*-1).  Thus (d_*) has
cohort one and

\[
 D_{R,d_*}=2^{d_*-2}(2^{d_*}+1).
\]

Its shortfall from the term used in (64) is

\[
 2^{R-d_*}-D_{R,d_*}
 =2^{d_*-2}(2^{d_*}-1)>2^{4t-3}.                 \tag{66}
\]

On the other hand, expansion of (56) gives

\[
 U-D_0
 =2^{4t-3}-2^{3t-2}+2^{2t-2}-2^{t-1}-1
 <2^{4t-3}.                                      \tag{67}
\]

Combining (63)--(67) yields

\[
 \boxed{
 \sum_{\substack{d>d_0\\ d\text{ visible}}}D_{R,d}<D_0.}  \tag{68}
\]

This conclusion does not use endpoint safety.  No subset of later ranks,
safe or unsafe, has enough total deficit mass to encode the forbidden
source.  In particular, the unmatched high block in (62) cannot be closed
by continuing forward.  The qualification “later” is essential: the
(R=44) carry in Section 10 uses the already earlier rank (12<13).  The
global propagation problem has therefore narrowed to a bank theorem:
exclude reuse of lower-rank deficit mass across a later forbidden pivot, or
charge that bank by a cocycle which cannot be spent twice.

Therefore no fixed lift by cohort phase together with the residue of the
odd unit modulo (2^H) can establish the missing propagation theorem: take
(t>H+3).  The exact block endpoint at which the impostor is exposed is
(2t-4).  Any successful carry invariant must retain an unbounded depth or
an equivalent endpoint/ancestry quantity, and must couple that quantity to
the strict phase loss in (46).

## 12. Reproduction

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/negacyclic_saturation_modulus.py
```

The script verifies (1)--(14) with exact integers over the stated parameter
range and checks the reduced equation on exhaustive small supports.  Those
finite checks are regression receipts only; the identities above are the
theorem.
