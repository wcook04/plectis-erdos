# The first renormalized type break for \(M(4,5)\)

Write

\[
 w_r=\frac1{2^r-1},\qquad M(a,b)=w_aw_b,qquad
 f(X)=\min\{r:w_r\le X\}.                         \tag{1}
\]

The first-generation compression theorem leaves two disjoint positive
cylinder cohorts at fronts \((83,84)\).  One cohort owns only the untouched
physical source \(M(25,29)\); the other owns the remaining fifteen sources.
The question is whether the synchronized-predecessor recut that occurred at
fronts \((77,77)\) repeats as a renormalized self-copy.

It does not.  The first new joint event is a different exact recut type.  The
two cohorts become staggered, merge all physical owners, and leave a single
cohort.  This rules out an induction whose state family consists only of the
three-cohort compression and the equal-front synchronized predecessor.

## 1. The two exact types at ranks \(83\) and \(84\)

Let \(C_{83}\) denote the owner-one cohort.  Two ordinary cylinder splits
give

\[
\begin{aligned}
 C_{83}
 &=M(25,29)-w_{54}-w_{79}\\
 &=M(29,54)+M(25,79)+M(54,79),
 \qquad f(C_{83})=83.                              \tag{2}
\end{aligned}
\]

After its next head,

\[
\begin{aligned}
 C_{104}:=C_{83}-w_{83}
 ={}&M(29,83)+M(54,83)\\
    &+M(25,79)+M(54,79),
 \qquad f(C_{104})=104.                            \tag{3}
\end{aligned}
\]

Thus this lineage retains an exact four-leaf cylinder-forest form and still
owns one physical source.

Let \(R_{84}\) be the other cohort, which owns the remaining fifteen
sources.  Its successive global heads are

\[
 84,88,92,94,98,99,100.                           \tag{4}
\]

Put

\[
 R_{103}=R_{84}-w_{84}-w_{88}-w_{92}-w_{94}
                 -w_{98}-w_{99}-w_{100}.          \tag{5}
\]

Exact comparison gives

\[
 f(R_{103})=103.                                  \tag{6}
\]

At every rank in (4), \(R_{84}\) and its successive residuals supply the
global greedy head without borrowing from \(C_{104}\).  Hence there is no
hidden nonlocal recut before the state

\[
 \bigl(C_{104},R_{103}\bigr),qquad
 (\text{fronts};\text{owner counts})=((104,1),(103,15)). \tag{7}
\]

## 2. A staggered-predecessor lemma

The next event has a reusable form.  Suppose \(U,V\) are disjoint positive
cylinder cohorts with fronts \(r+2\) and \(r+1\).  If

\[
 w_r+w_{r+3}\le U+V<w_r+w_{r+2},                  \tag{8}
\]

then neither cohort reaches \(w_r\), but their ownership-closed union emits
\(w_r\) and leaves a positive cylinder cohort of front \(r+3\):

\[
 H=U+V-w_r,qquad f(H)=r+3.                       \tag{9}
\]

The front assertion follows from (8).  Exact positivity in the cylinder
cone follows by refining the integer cylinder combination for
\(U+V-w_r\) to common coordinate multiples.  This is a width-two recut, but
it is not the synchronized-predecessor lemma: the incoming fronts are
different, and neither old head is emitted.

For (7), the exact inequalities are

\[
 w_{102}+w_{105}
 \le C_{104}+R_{103}
 <w_{102}+w_{104}.                                \tag{10}
\]

Also

\[
 C_{104}<w_{102},\qquad R_{103}<w_{102}.          \tag{11}
\]

Therefore their union has global front \(102\), and

\[
 H_{105}=C_{104}+R_{103}-w_{102},qquad
 f(H_{105})=105.                                  \tag{12}
\]

This recut merges the owner partition \((1,15)\) into a single cohort
owning all sixteen physical first-front sources.

## 3. Failure of the self-copy induction

For a cohort \(X\), define its exact front-normalized mass by

\[
 \mu(X)=(2^{f(X)}-1)X.                            \tag{13}
\]

An ownership-sensitive renormalized type records the owner count together
with \(\mu(X)\).  Before (12), the state has two types with owner counts
\((1,15)\).  Afterwards it has one type with owner count \(16\).  Moreover,
exact rational comparison shows that \(\mu(H_{105})\) is different from
the normalized masses of \(C_{83},R_{84},C_{104}\), and \(R_{103}\).

Consequently the transition at rank \(102\) is not a scaled copy of either
the \((83,84)\) state or the equal-front \((77,77)\) recut.  Any finite-state
induction for \(1/465\) must include a third transition type:

\[
 (r+1,r+2)\longrightarrow r\longrightarrow r+3,  \tag{14}
\]

with complete owner merger.  The earlier two-type renormalisation is not
closed.

This does not rule out a larger finite automaton.  After (12), physical
ownership is simpler—there is only one cohort—but the remaining Boolean
condition is the fatal-gap inequality

\[
 X<2w_{f(X)}                                      \tag{15}
\]

at every subsequent greedy subtraction.  Proving (15) for the one-cohort
orbit, or finding its first violation, is the exact next boundary.

## 4. Exact conservation

Together with the earlier prefix through rank \(79\), the additional atoms
are

\[
 83,84,88,92,94,98,99,100,102.                   \tag{16}
\]

The exact audit verifies

\[
 M(4,5)=\sum_{r\in\mathcal P_{102}}w_r+H_{105},
 \qquad f(H_{105})=105,                           \tag{17}
\]

where \(\mathcal P_{102}\) is the resulting Boolean prefix.  Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_first_type_break.py
```

The script uses exact rational arithmetic for every front, cylinder identity,
normalised-type comparison, and conservation equality.
