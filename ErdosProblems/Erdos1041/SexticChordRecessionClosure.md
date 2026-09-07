# A recession argument closes the sextic chord band

Status: an ordinary proof with a complete exact integer interval/Bernstein
certificate, 2026-09-05. This closes the homogeneous-model producer
`sextic_unrestricted_chord_covering_band`. It is not a Lean-checked theorem,
an actual-polynomial transfer theorem, or a solution of Erdős #1041.

## Result and reason for the change of object

Let
\[
 H_{A,B,C}(z)=\operatorname{Re}(Az+Bz^2+iCz^3-\bar Bz^4-\bar Az^5-z^6),
 \qquad A,B\in\mathbb C,\quad C\in\mathbb R.
\]
Write \(\omega=e^{\pi i/3}\). **Theorem.** If \(|B|=1\), then for every
\(A\) and every real \(C\), one of the six adjacent chords
\([\omega^j,\omega^{j+1}]\) satisfies
\[
                       H_{A,B,C}\le-1/256
\]
on its entire length. That length is exactly one.

The case \(|A|\le1\) is Theorem 3 of
[SexticChordCoveringCriterion.md](SexticChordCoveringCriterion.md). Here we
prove the entire complementary range \(|A|\ge1\), including the former gap
\(1<|A|<226/(32-8\sqrt3)\). The useful step is to stop following the
minimizing chord as \(|A|\) changes. Instead select an opposite-parity pair at
\(|A|=1\) whose *combined recession bound* is nonpositive. That same pair then
works at every larger magnitude. A noncompact three-parameter search becomes
a compact two-phase certificate.

This is a consequence of the corpus's chord normal form and parity covering
criterion, not a claim of an independently new general mathematical method.
External novelty and independent review have not been assessed.

## The recession lemma

Put \(A=\lambda a\), \(|a|=1\), \(\lambda\ge1\), and
\(\theta_j=(2j+1)\pi/6\). On the chord
\(z_j(x)=e^{i\theta_j}(\sqrt3+ix)/2\), \(-1\le x\le1\), define
\[
\begin{aligned}
 L_j(x)&=10\sqrt3\operatorname{Re}(ae^{i\theta_j})(5-x^2)
           +2\operatorname{Im}(ae^{i\theta_j})x(29-x^2),\\
 M_j(x)&=x^4-44x^2+91
       +4\operatorname{Re}(Be^{2i\theta_j})(21-x^2)
       +16\sqrt3\operatorname{Im}(Be^{2i\theta_j})x.
\end{aligned}
\]
The source identity is
\[
 64H(z_j(x))=-64+(1-x^2)
       [M_j(x)+\lambda L_j(x)-24\sqrt3(-1)^jC].
\]
For the desired margin define, on \(|x|<1\),
\[
 W_j^{*}(x;\lambda)=M_j(x)+\lambda L_j(x)
                         -\frac{255}{4(1-x^2)}.
\]
Thus chord \(j\) has \(H\le-1/256\) precisely when
\(\sup_x W_j^{*}(x;\lambda)\le24\sqrt3(-1)^jC\). Its endpoints already
have \(H=-1\).

**Lemma.** Suppose an even \(j\) and an odd \(k\) have real bounds
\[
 L_j\le s_j,\quad L_k\le s_k,\qquad
 W_j^{*}(\cdot;1)\le T_j,\quad W_k^{*}(\cdot;1)\le T_k,
\]
with \(s_j+s_k\le0\) and \(T_j+T_k\le0\). Then, for every \(\lambda\ge1\)
and every real \(C\), one of these two chords has the desired margin.

*Proof.* The respective threshold bounds are
\(T_j+(\lambda-1)s_j\) and \(T_k+(\lambda-1)s_k\). Their sum is nonpositive.
The even chord is safe on the upper half-line in \(24\sqrt3 C\) beginning
at its threshold; the odd chord is safe on the lower half-line ending at
the negative of its threshold. The half-lines overlap. The two suprema may
be attained at different points; no common optimizer is assumed. ∎

## Finite certificate of the lemma's hypotheses

The verifier is
[check_erdos1041_chord_recession_closure.py](scripts/check_erdos1041_chord_recession_closure.py).
Its acceptance calculations use only Python integers and exact rational
numbers. Floating-point sampling suggested the lemma but is not an input to
its verification.

1. Rotating the variable by \(\omega^k\) replaces
   \((A,B,C)\) by \((A\omega^k,B\omega^{2k},(-1)^kC)\). Conjugating the
   variable replaces them by \((\bar A,\bar B,-C)\). Both permute adjacent
   chords. We may therefore assume \(0\le\arg a\le\pi/6\), with \(B\)
   still arbitrary on the unit circle.
2. Use the exact unit-circle parametrization
   \(u(t)=(1-t^2+2it)/(1+t^2)\). It suffices to cover
   \(a=u(t)\), \(0\le t\le1/3\), and
   \(B=i^q u(v)\), \(0\le v\le1\), \(q=0,1,2,3\).
   Indeed \(\tan(\pi/12)=2-\sqrt3<1/3\); the slight excess in the first
   interval is harmless. Each closed quadrant is covered, including seams.
3. Begin with 16 equal intervals in \(t\) and 32 in \(v\), for each of
   four quadrants. At each rational box center enclose every coefficient in
   units of \(2^{-40}\), using the exact enclosure
   \(\lfloor\sqrt{3\,2^{80}}\rfloor/2^{40}\le\sqrt3
     \le(\lfloor\sqrt{3\,2^{80}}\rfloor+1)/2^{40}\).
   Every arithmetic operation rounds outward by integer floor or ceiling.
4. On 16 equal subintervals of \([-1,1]\), convert the cubic \(L_j\) and
   the degree-six polynomial
   \(P_j=(1-x^2)(M_j+L_j)-255/4\) to Bernstein form. Upper controls bound
   \(L_j\). For \(P_j-T(1-x^2)\), each Bernstein control of \(1-x^2\) is
   nonnegative. Each positive control gives an exact rational lower bound
   on \(T\); zero controls have strictly negative corresponding controls
   of \(P_j\). Taking the ceiling of the largest ratio gives an integer
   \(T_j\) with \(W_j^{*}(\cdot;1)\le T_j\).
5. The center bounds extend to whole boxes. The first- and second-mode
   kernel norms are at most 90 and 85, respectively, because their squares
   are
   \[
   7500+364x^2+68x^4+4x^6\le7936<90^2,
   \qquad7056+96x^2+16x^4\le7168<85^2.
   \]
   Also \(|u'(t)|=2/(1+t^2)\le2\). A box of full widths \(d_t,d_v\)
   therefore has recession drift \(90d_t\) and threshold drift
   \(90d_t+85d_v\). These are added to each chord's respective bounds.
6. Accept a box only when at least one of its nine opposite-parity pairs
   satisfies *both* inequalities in the lemma after these drifts are added.
   Otherwise bisect the coordinate with larger drift contribution. Initial
   boxes cover the domain, and each bisection is an exact cover by closed
   children. Exhausting the stack with every leaf accepted proves the
   continuous-domain assertion.

The complete run accepts 2,070 boxes: the initial 2,048 boxes require just
22 bisections, each at depth one. The least certified pair recession slack
is \(25/4\), and the least threshold slack is \(19/32\). Thus acceptance
does not depend on equality or a numerically unresolved sign. The ordered
leaf-certificate SHA-256 is
`af51c86d18b20c08c4cf7e55a126793c4a9f0777a30a333d94352be8044c74f2`.

Run from the repository root:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_chord_recession_closure.py --audit
```

The source normal form was also reconstructed independently by symbolic
expansion of the original complex polynomial on all six chords. The circle
identity and the Bernstein endpoint identities were checked with exact
fractions. These checks support the implementation; the continuous-domain
proof is the enclosure argument above. The certificate has not been checked
by Lean or an independent reviewer.

The `--audit` option reproduces 926 exact symbolic-identity, coefficient-
enclosure and Bernstein-reconstruction checks with SymPy. Omitting that
option runs the full continuous-domain certificate with the standard library
alone. The ten relevant exact checks in the earlier unit-band verifier also
pass, including its six-piece certificate of \(G_1\ge1/4\).

## Consequences and exact limits

Combining this theorem with the source's small-coefficient theorem replaces
the two-chart homogeneous construction at \(|B|=1\) by one adjacent-chord
family for all \(A,C\). The available uniform margin is \(1/256\), with
connector length one and length slack one against the budget two. The old
global figures \(1/768\) and \(1/16\) for the ray-chart interface are no
longer needed on this normalized model.

The first-mode ray construction retains its other uses. In particular, the
theorem does not permit rescaling an arbitrary model to \(|B|=1\) while
silently fixing the coefficient of \(-z^6\): that changes the polynomial.
The known counterexamples below \(|B|=9/14\), and the pure-cubic face,
remain outside this theorem. No nonlinear source reconstruction, outer
root-to-chord continuation, all-degree neighborhood, or unrestricted
lemniscate theorem follows without its own proof.

## Research and review receipt

`selected_gate`: discriminating lemma followed by exact verification.

`candidate_attacks`: (i) #243 primitive-record growth: strong exact cocycle
and protected-prime barriers, but arbitrary finite clean-rise fixtures defeat
local charging; probe a global protected-source inequality and stop at a
finite-prefix-only reformulation. (ii) #257 denominator-21 greedy recurrence:
exact fatal-branch reduction and long exact replay, but finite returns do not
supply cofinality; probe a recurrence invariant and stop if it merely
restates membership. (iii) #1041 sextic chord thresholds: exact normal form,
parity decoupling and strict measured margins, but the fixed antipodal pivot
has a proved finite ceiling; probe a pair with a nonpositive combined
recession bound. Candidate (iii) provided the cheapest decisive test.

`selected_probe`: phase-dependent opposite-parity pair at unit first-mode
magnitude, with two separate upper bounds; `probe_falsifier`: a phase for
which every recession-admissible pair has positive threshold sum.
`rejected_as_rehash`: extending the old fixed-pivot band or merely increasing
the coefficient sweep horizon. `stop_or_pivot_condition`: an uncovered exact
phase box after refinement; none remained.

`tao_pipeline_receipt`: generation → verification and internal understanding;
artifact: this note and its exact checker; understanding delta: a recession
bound converts the unbounded chord range to a compact phase problem;
verification: complete exact computational certificate plus the displayed
ordinary implication proof; publication/review: internal, no independent
review; canonicalization: subsumes the old open middle band under one
normalized chord theorem; downstream bottleneck: source-specific nonlinear
transfer; next owner: the #1041 proof lane.

`tao_writing_review`: internal theorem note for a reader comfortable with
polynomial inequalities; promise: an inspectable closure of one named
auxiliary producer. The hard step is existence of a pair satisfying both
recession and threshold inequalities, resolved by the complete enclosure
certificate rather than hidden inside a sampled maximum. The external
novelty boundary is explicit; the internal map is normal form → recession
lemma → phase certificate → normalized-model consequence. Notation agrees
with the source note. The main cold reread checked endpoint factors, parity
under symmetry, distinct maximizers, outward rounding, and the forbidden
rescaling of the sextic coefficient. No figures or bibliography were added;
source links and the reproduction command identify the actual dependencies.

The source-specific successor is captured in Task Ledger as
`cap_quick_use_the_closed_sextic_chord_range_in_the_af1fb828a7e5`.
