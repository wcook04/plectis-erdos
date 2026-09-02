# A transported borrow suffix can be discharged into the fatal corridor

Put
\[
 w_n=\frac1{2^n-1},\qquad M(2,H)=\frac1{3(2^H-1)}.
\]
The coefficient transport law for a packet residual is
\[
 B\equiv2^j-3\pmod {2^k}.
\]
When \(j\ge k\), the transported suffix is \(2^k-3\): all its bits are
one except bit 1.  It is therefore natural to ask whether the lower part of
this forced suffix always supplies the carry tax for its highest adjacent
pair.  The answer is no, even at height 15.

Take \(k=4\).  The suffix is
\[
 2^4-3=13=2^3+2^2+2^0.                            \tag{1}
\]
At anchored height \(H=15\), the top pair has value
\[
 (2^3+2^2)M(2,15)=12M(2,15),                      \tag{2}
\]
and its front ranks are 14 and 15.  The forced lower complement is the
single packet \(M(2,15)\).

Now extract the five future Boolean atoms
\[
 F=\{17,19,21,23,25\}
\]
from that lower complement.  Exact arithmetic gives
\[
 M(2,15)-\sum_{n\in F}w_n
 =\frac{187109759089667485459118014}
 {18375676354888732285633470747770427}>0.          \tag{3}
\]
Nevertheless, after this positive extraction the complete suffix residual
lies strictly in the rank-14 zero-buffer corridor:
\[
 2w_{14}
 <13M(2,15)-\sum_{n\in F}w_n
 <w_{13}.                                         \tag{4}
\]
The two margins in (4) are
\[
 \frac{5101896790648198873453573400}
 {790154083260215488282239242154128361}>0
\]
and
\[
 \frac{149778722190121591840742784269}
 {150515165022893606151623758894987567557}>0,
\]
respectively.

Thus the almost-all-ones suffix created by the exact \(-3\) borrow does not
carry a hereditary solvency certificate.  Its forced lower complement can be
spent on later distinct atoms while leaving the top adjacent pair inside the
fatal interval.  This does not produce a fatal state for the complete
\(M(2,3)\) genealogy: higher coefficient blocks and sibling cohorts remain
outside the four-bit suffix.  It shows that the complete first-wave theorem
in `FirstWaveZeroBufferSolvency.md` depends essentially on the whole external
cohort.  It cannot be iterated one transported suffix at a time.

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/transported_suffix_solvency_nogo.py

to check (1)--(4) in exact rational arithmetic.
