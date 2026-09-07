# The first LCM lift obstructs the cylinder-only Boolean rewrite

Write
\[
  w_r=\frac1{2^r-1},\qquad M(a,b)=w_aw_b.
\]
This note audits the global rewrite question left open in
`PositiveCylinderBooleanisationAudit.md`.  The rewrite grammar considered here
has only the following two operations.

For one cylinder of stop \(s=a+b\), ordinary splitting gives
\[
  M(a,b)=w_s+M(s,b)+M(a,s).                         \tag{1}
\]
For two cylinders of the same stop \(s\), the LCM lift gives
\[
  M(a,b)+M(c,d)
   =w_{s-1}+A M(s,L)+\text{three child cylinders}, \tag{2}
\]
where \(a+b=c+d=s\), an endpoint \(e\) of one parent is chosen,
\[
 L=\operatorname{lcm}(e,s-1),\qquad
 A=\frac{2^L-1}{2^e-1}-\frac{2^L-1}{2^{s-1}-1}>0,
\]
and every cylinder on the right has stop greater than \(s\).  Atoms emitted by
(1) and (2) are taken to be irrevocable.  This is exactly the positive
cylinder-only system proposed in the earlier audit; a rule which later absorbs
duplicate atoms is outside the present grammar.

## 1. Fixed-stop capacity

Suppose a schedule contains \(C\) cylinders with the same stop \(s\).  Every
rewrite which consumes one of these cylinders has one of two forms:

* an ordinary split consumes one cylinder and emits \(w_s\);
* an LCM collision consumes two cylinders and emits \(w_{s-1}\).

If the emitted atoms are Boolean, at most one ordinary split and at most one
LCM collision can be used at this stop.  Consequently at most three of the
\(C\) cylinders can ever be consumed.

Equivalently, if \(x\) pair rewrites and \(y\) ordinary splits eliminate the
cohort, then
\[
  2x+y=C.
\]
Booleanity requires \(x\leq1\) and \(y\leq1\), and hence \(C\leq3\).
This argument does not depend on rewrite order, on the endpoints of other
cylinders, or on whether the cohort is paired internally or with other
stop-\(s\) cylinders.  Pairing a cohort member with an outside cylinder still
emits one copy of \(w_{s-1}\).

Thus a cohort of four equal-stop cylinders is already incompatible with a fair
Boolean schedule.  If the schedule processes a fourth member, it repeats one
of the atoms \(w_{s-1},w_s\).  If it never processes that member, the unresolved
cylinder mass stays positive.

## 2. The first collision creates a fatal cohort

Starting from \(M(2,3)\), ordinary splitting before the first collision emits
\[
  w_5,w_7,w_8,w_9.
\]
The first repeated stop is \(11\), with the two cylinders
\[
  M(8,3),\qquad M(2,9).                              \tag{3}
\]
Splitting them separately would emit two copies of \(w_{11}\).  Therefore a
Boolean schedule in the stated grammar must apply (2) to this pair.  It emits
\(w_{10}\), as required by the exact greedy prefix, and it may choose one of
the four endpoints \(e\in\{2,3,8,9\}\).

The resulting LCM cohorts are
\[
\begin{array}{c|c|c|r}
e&L&\text{lifted cylinder and stop}&A\\ \hline
2&10&M(11,10),\ 21&340\\
3&30&M(11,30),\ 41&152342088\\
8&40&M(11,40),\ 51&3237018880\\
9&90&M(11,90),\ 101&1212475681849964898811392.
\end{array}                                           \tag{4}
\]
Every choice creates at least \(340\) cylinders with one common stop.  Section
1 applies immediately.  A fair continuation must eventually process at least
four of them and hence emit a duplicate atom.  A continuation which preserves
Booleanity can process at most three and leaves mass at least
\[
  (A-3)M(11,L)>0.                                    \tag{5}
\]
Its unresolved cylinder mass therefore cannot tend to zero.

This proves that no fair global schedule starting at \(M(2,3)\) can satisfy
both requirements under operations (1) and (2): Boolean emitted atoms and
vanishing unresolved cylinder mass.  The obstruction is created by the first
LCM lift.  It is only realised at stop \(21,41,51\), or \(101\), depending on
the endpoint choice, but no later scheduling choice can remove it.

## 3. Why the lifted stop is not a mass escape

The coefficient in (2) satisfies the exact identity
\[
  A w_L=w_e-w_{s-1}.                                 \tag{6}
\]
Hence the whole lifted cohort has mass
\[
  A M(s,L)=M(e,s)-M(s-1,s),                          \tag{7}
\]
which is independent of the displayed lift rank \(L\).  The LCM operation
moves the label far to the right by encoding the old mass as exponentially
many equal cylinders.

One way to record this is the dyadic height
\[
  H(mM(a,b))=a+b-\log_2 m.
\]
For the lifted block, elementary estimates give
\[
  s+e-1 < H(A M(s,L)) < s+e+2.                       \tag{8}
\]
Indeed,
\[
  2^{-(e+1)}<w_e-w_{s-1}<2^{-(e-1)}
\]
and \(2^{L-1}<2^L-1<2^L\).  Thus the apparent jump from stop \(s\) to
stop \(s+L\) raises the dyadic height only to within a constant of \(s+e\).
At the first collision, the four possible effective heights remain near
\(13,14,19,20\), even though the displayed stops range from \(21\) to \(101\).

This is the common mass/multiplicity mechanism: stop labels escape while the
mass does not.  Any termination argument based only on the minimum displayed
stop misses the exponential multiplicity created by the LCM quotient.

## 4. Allowing temporary duplicate atoms

The fixed-stop argument assumes that emitted atoms remain Boolean at every
intermediate stage.  A stronger rewrite system may retain duplicate atoms and
carry them later by
\[
  2w_r+M(r-1,r)=w_{r-1}.                             \tag{9}
\]
This changes the local obstruction: a large stop-\(s\) cohort may emit many
copies of \(w_{s-1}\), provided the rest of the frontier eventually supplies
enough copies of \(M(s-2,s-1)\).

The LCM cohort does not supply this credit from its own descendants.  Splitting
a stop-\(s\) cylinder creates children \(M(e,s)\), and these may be decomposed
as
\[
 M(e,s)=M(s-1,s)+A M(s,L).                           \tag{10}
\]
The extracted cylinder \(M(s-1,s)\) carries duplicates of \(w_s\).  A pair
rewrite at stop \(s\), however, emits \(w_{s-1}\), whose next carry requires
\(M(s-2,s-1)\).  All later split and lift coordinates are at least \(s\), so
the cohort cannot create this one-rank-earlier credit.  Such credit must come
from an independent part of the frontier.

This observation can be made into a conserved source count.  Fix \(r\).  A
new cylinder with coordinate \(r\), and hence a possible source of
\(M(r-1,r)\), can first appear only in one of two ways:

1. a stop-\(r\) parent is split, creating two children \(M(e,r)\);
2. an earlier LCM lift has \(L=r\).

Once both coordinates of a cylinder exceed \(r\), no forward split or LCM
lift can create coordinate \(r\).  If \(e\nmid r-1\), (10) extracts exactly
one \(M(r-1,r)\) from the lineage \(M(e,r)\); its residual is \(M(r,L)\) with
\(L>r\) and cannot return.  If \(e\mid r-1\), the exceptional divisor pulse is
\[
  M(e,r)=\frac{2^{r-1}-1}{2^e-1}M(r-1,r).            \tag{11}
\]
Thus the available rank-\(r\) credit is determined by the stop-\(r\) frontier,
the solutions of \(\operatorname{lcm}(e,n-1)=r\), and the divisors of
\(r-1\).  This is a coordinate potential: later cylinders cannot increase it.

### 4.1 The endpoint choice \(e=2\) fails at the first backward rank

Choose \(e=2\) in the first stop-11 collision.  The 340 lifted cylinders have
stop 21.  Eliminating their duplicate emissions creates 170 copies of
\(w_{20}\).  The independent ordinary frontier has two stop-20 parents,
\[
  M(9,11),\qquad M(3,17).
\]
Their four children supply four copies of \(M(19,20)\).  Since 19 is prime,
none of the four endpoints gives a divisor pulse.  There is no earlier lift
with stop 20, and a lift with coordinate \(20\) would require either
\((n,e)=(6,4)\) or \((11,4)\); neither collision exists with endpoint 4.
Splitting the two parents adds two local copies of \(w_{20}\), so the best
possible use of the four credits leaves
\[
  170+2-2\cdot4=164                                  \tag{12}
\]
copies of \(w_{20}\).  At most one can remain in a Boolean normal form.

The corresponding direct-credit counts for \(e=8\) and \(e=9\) are
\[
\begin{array}{c|c|r|r|r|r}
e&r&\text{incoming }w_r&\text{stop-}r\text{ parents}
 &\text{available credits}&\text{atoms left}\\ \hline
2&20&170&2&4&164\\
8&50&1618509440&4&8&1618509428\\
9&100&606237840924982449405696&6&12
 &606237840924982449405678.
\end{array}                                           \tag{13}
\]
For \(r=50\), the only possible direct coordinate-50 lift is at stop 26
with endpoint 2 or 10; neither endpoint occurs there.  The only lift whose
resulting cylinder has stop 50 would require the single stop-8 cylinder to
collide.  Also \(49=7^2\), but no stop-50 child has endpoint 7.

For \(r=100\), direct coordinate-100 lifts require endpoint 4 or 20 at stop 26 or
51.  Those endpoints are absent after the stop-11 choice \(e=9\).  Potential
extra stop-100 cohorts could only come from stop 12 with endpoint 8 or stop 34
with endpoint 2, 6, or 22; none is available.  No endpoint of the six
stop-100 parents divides \(99\).  Therefore every one of their twelve children
supplies only one adjacent credit.

The last two rows are exact deficits for the ordinary frontier plus direct
coordinate and exact-stop lifts.  They are not yet impossibility proofs for the
recursive grammar: a lift born below rank 50 or 100 can have descendants whose
first emission is the target rank, enlarging the stop-rank frontier.  That
ancestral closure is trivial for \(r=20\), because the first lift already has
stop 21, but it has not been exhausted for \(r=50,100\).

### 4.2 The choice \(e=3\) has two resonances, then fails at rank 38

The choice \(e=3\) creates 152342088 copies of \(M(11,30)\).  Normalizing this
cohort forces 76171044 copies of \(w_{40}\).  Unlike the other three choices,
the independent frontier contains a matching LCM pulse.  If the two stop-21
cylinders
\[
  M(8,13),\qquad M(2,19)
\]
are split, the child \(M(8,21)\) satisfies
\[
 M(8,21)=M(20,21)+4310761728M(21,40).                \tag{14}
\]
Each \(M(21,40)\) can supply one \(M(39,40)\), so (14) contains far more than
the 38085522 credits needed to carry the rank-40 atoms.

This pulse is forced if the rank-40 carry is to be funded within the audited
grammar.  The equations \(\operatorname{lcm}(e,n-1)=40\) give only
\((n,e)=(9,5),(11,8),(21,8)\).  Stop 9 has one parent, and the choice \(e=3\)
at stop 11 excludes the second pair.  Lifts born below stop 40 whose primitive
descendants emit at 40 can arise only at stops 5, 6, or 7, none of which is a
collision.  Thus the stop-21 pulse is the only source large enough, and it
requires ordinary splitting of the two stop-13 parents to retain both branches
in (14).

Those carries produce 38085522 copies of \(w_{39}\).  A second exact resonance
then occurs on the retained endpoint-2 branch:
\[
  M(2,39)=91625968981M(38,39).                       \tag{15}
\]
Splitting the parent \(M(2,37)\) emits one additional \(w_{39}\).  Keep that
one atom and use (15) to carry the other 38085522 copies.  This produces
19042761 copies of \(w_{38}\).

The next layer has no resonance.  After the first choice \(e=3\), the only
stop-38 parents outside the lifted cohort are
\[
  M(9,29),\qquad M(5,33).                            \tag{16}
\]
Their four children each supply one \(M(37,38)\), because 37 is prime.  No LCM
lift has stop 38.  The equation \(L=38\) has the sole admissible parameter pair
\((n,e)=(20,2)\), but the modified stop-20 frontier consists only of
\(M(9,11)\), so that pulse cannot occur.  Splitting (16) adds two local atoms;
even after all four credits are used, at least
\[
  19042761+2-2\cdot4=19042755                       \tag{17}
\]
copies of \(w_{38}\) remain.

There is one apparent lower-lift route into stop 38 at stop 13: choosing
endpoint 2 there creates \(1364M(13,12)\), and the primitive expansion of
\(M(13,12)\) has an emission at 38.  That choice consumes the two stop-13
parents, so it destroys the stop-21 pair required by (14).  All other lower
lifts with a descendant emission at 38 would have to start at stops 5, 6, 8,
or 10, where no collision is available.  Hence a schedule either lacks the
rank-40 credit or reaches the rank-38 deficit (17).

Equations (12)--(17) exclude the choices \(e=2\) and \(e=3\) even after
recursive adjacent-cylinder carries are allowed.  The choice \(e=3\) is
important because the first two carry layers really are funded: the failure is
not a crude mass shortage.  It occurs when the backward atom cascade reaches a
rank whose divisor and LCM sources cannot replenish the coordinate-credit
potential.  The choices \(e=8\) and \(e=9\) retain the large direct deficits in
(13), but their full lower-lift ancestral closures remain open.

## 5. Exact boundary of the negative result

The argument disproves the cylinder-only normalization with irrevocable atoms.
For its extension by the literal adjacent-credit carry (9), it disproves the
first endpoint choices \(e=2,3\) and isolates exact direct deficits for
\(e=8,9\); it does not yet exclude all recursive schedules.  It also does not
disprove the existence of a Boolean representation of \(1/21\).  A larger
rewrite system could still combine several non-adjacent cylinders into one
credit, recut a cylinder across coordinate levels, or normalize a whole cohort
without passing through the forced binary chain in (9).  None of those
operations belongs to the audited grammar.

In particular, this note does not apply the adjacent-credit deficit to a
whole-cohort binary-block rewrite.  Such a rule treats the coefficient of a
cylinder in one step rather than carrying its atom multiplicities one rank at a
time.  The next section audits the proposed binary decomposition of the first
340-cylinder cohort separately.

## 6. The first binary-block cohort collides with the global frontier

For a power block, exact cross-multiplication gives
\[
  2^jM(a,b)>w_{a+b-j}
  \quad\Longleftrightarrow\quad
  2^a+2^b>2^j+1.                                    \tag{18}
\]
Since
\[
  340=2^8+2^6+2^4+2^2,
\]
applying (18) separately to the four blocks of \(340M(11,10)\) emits
\[
  w_{13},\quad w_{15},\quad w_{17},\quad w_{19}.     \tag{19}
\]
The four positive remainders have first affordable ranks 23, 25, 27, and 29.
Their sum also has first affordable rank 23:
\[
 w_{23}
 \leq340M(11,10)-(w_{13}+w_{15}+w_{17}+w_{19})
 <w_{22}.                                            \tag{20}
\]
Thus the block residual itself is genuinely delayed; it cannot repair a
collision at one of the ranks in (19).

The other frontier is not delayed.  The three ordinary children retained by
the first \(e=2\) collision have emissions at ranks 17 and 19: respectively
\(M(3,14)\) and the root \(M(8,11)\).  The untouched frontier branches add one
emission at each of ranks 13, 17, and 19.  Before any anticipatory recut, the
combined multiplicities at the four block ranks are therefore
\[
\begin{array}{c|cccc}
r&13&15&17&19\\ \hline
\text{binary block}&1&1&1&1\\
\text{ordinary frontier}&1&0&2&2\\
\text{total}&2&1&3&3.
\end{array}                                          \tag{21}
\]

There is an even earlier incompatibility if the atoms in (19) are declared
final.  The exact selected prefix through rank 10 is
\(5,7,8,9,10\), and its remainder is larger than \(w_{11}\), so every Boolean
completion must select rank 11.  After the four atoms in (19) are subtracted
as well, the remaining global mass satisfies
\[
 w_{12}
 <\frac1{21}-\sum_{r\in\{5,7,8,9,10,13,15,17,19\}}w_r
 <w_{11}.                                            \tag{22}
\]
It can no longer pay the forced atom \(w_{11}\).  Hence the four binary-block
atoms cannot be irrevocable members of a positive Boolean normal form.

This does not rule out a whole-cohort system in which the atoms in (19) are
provisional and may be recut together with the ordinary frontier.  It identifies
what that system must do: recut the multiplicities \(2,1,3,3\), recover the
forced rank 11 despite (22), and preserve the delayed positive remainder (20).
That is a new nonlocal operation, not an instance of the binary-block extraction
or the adjacent carry (9).

The companion script verifies the first frontier, all four exact lift
identities, the fixed-stop capacity calculation, the recursive credit receipts,
and (18)--(22):

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/lcm_lift_global_rewrite_obstruction.py
```

All large integers in (4) are exact.  The proof of the obstruction uses only
the inequality \(A\geq4\); the computation is a receipt, not a finite-search
substitute for the argument.
