# Draft: psh reduction and extremal taxonomy for the separatrix aggregate

WIRING (all proved in-corpus, verified at source this session): by
`AttachmentAwareReeb.md` Corollary 3a, `Lam(f) <= min_c L(c) <= (1/m) Sigma_c
L(c)` for ray-separated `f`; by its Corollary G (density of ray-separated
polynomials in `K_n`) composed with `GenericSufficiencyClosure.md` Theorem L
and Corollary S, proving `min_c L(c) <= 2` on ray-separated `K_n` proves
Erdős 1041 in degree `n`.  Hence

    (AGG)  Sigma_c L(c) <= 2(n-1)   on ray-separated K_n
    ==>    Erdős 1041 in degree n,

with no further bookkeeping: density, lower-semicontinuous closure,
containment of the canonical arcs, and open-disk strictification are all
already landed.  (AGG) is the single remaining inequality on this lane, and
this draft reduces IT further.

Target row (global combined charge, `critical_point_selection_with_inverse_
ray_length_control`): for monic `f`, simple roots in a disk of radius `R_MEC`
(minimum enclosing circle of the roots),

```
(AGG-MEC)    Sigma_c L(c)  <=  2 (n-1) R_MEC,
```

sum over all critical points, `L(c)` = two-arm inverse-ray length.  Implies
`min_c L(c) <= 2 R_MEC`; with the admissibility bookkeeping (below) it implies
the parent.  Equality on the radial family `(z-tau)^n - lambda` (each of the
`n-1` coincident hubs carries `L = 2r`, `R_MEC = r`).

## Proposition PSH (per-cell plurisubharmonicity of the aggregate)

Let `Lambda` be a connected open set of configurations `a = (a_1..a_n)` in
`C^n` on which roots and critical points are simple, critical values nonzero,
and each hub's two resolved arms extend over `u in [0,1]` without meeting any
other critical point (wall-free cell, fixed combinatorics).  Then each
`a -> L(c_k(a))` and hence `a -> Sigma_k L(c_k(a))` is plurisubharmonic on
`Lambda`.

Proof sketch (rigorous; adapts the corpus's HubModuliReduction §5 from the
first-merge beta-chart to all hubs in root coordinates).  At a simple critical
point, `c_k(a)` and `w_k(a) = f_a(c_k(a))` are holomorphic.  The resolved arm
equation `f_a(Z) = w_k(a)(1 - u^2)`, `Z(0) = c_k(a)`, `Z'(0) = ± sqrt(-w_k/A_k)`
has a jointly holomorphic solution `Z_k^pm(u; a)` on a complex neighbourhood
of `[0,1] x Lambda'` for every `Lambda' cc Lambda`: the `u = 0` square root is
resolved by the quadratic chart (`A_k = f''(c_k)/2 != 0`), and on `(0,1]` the
implicit function theorem applies since the arm avoids critical points
(wall-free hypothesis).  Note ties `|w_i| = |w_j|` are NOT walls: the segment
`[0, w_k(a)]` rotates holomorphically with `w_k(a)`; only an arm passing
through another critical point breaks the continuation.  Define
`G_k^pm : Lambda -> L^1([0,1])`, `a -> d/du Z_k^pm(.; a)`: holomorphic
Banach-valued.  Then `L(c_k) = ||G_k^+||_1 + ||G_k^-||_1`, and the norm of a
holomorphic Banach-valued map is plurisubharmonic (Hahn-Banach: it is the
upper envelope of the psh moduli `|phi o G|`, `phi` in the unit ball of the
dual, locally uniformly bounded).  Sums of psh are psh.  QED

Numeric falsification test passed: sub-mean-value along 8/8 random
holomorphic disks (n = 3..5, eps = 0.01, 12-point circles), mean minus center
between `+9.4e-5` and `+5.3e-3` (always nonnegative).

## Corollary MAX (extremal pushed to the boundary strata)

Fix the translation slice `Sigma a_j = 0` and the compact
`{R_MEC(a) <= 1}`.  Within the closure of any wall-free cell, the supremum of
`Sigma_c L(c)` is approached on the union of:

- (circle stratum) configurations with `R_MEC = 1` — at least two roots on the
  unit MEC circle; iterating the maximum principle in each off-circle root
  variable pushes every root to be either on the MEC circle or wall-locked;
- (wall strata) configurations where some arm passes through another critical
  point — equivalently the gradient field of `log|f|` has a SADDLE CONNECTION
  (`w_j` on the ray `[0, w_k]` with the lift meeting `c_j`);
- (degenerate strata) root or critical collisions (complex codimension one).

Wall structure: on a wall, the arm of `c_k` decomposes as (arm of `c_j`) +
(saddle connection `c_j -> c_k`); recursion within wall strata pushes to
configurations with maximal saddle-connection spines.  The radial family is
the common corner: all saddles coincide (every wall collapsed) and all roots
on the MEC circle.  The Chebyshev-type spines (extreme roots on the circle,
interior roots wall-locked) are the other maximal stratum.

## Consequence (conditional reduction)

(AGG-MEC) for all configurations follows from:

1. (AGG-MEC) on circle-locked configurations (roots on the unit MEC circle) —
   self-inversive-adjacent structure; corpus concyclic machinery applies;
2. (AGG-MEC) on maximal saddle-connection spines (Chebyshev-type) — here the
   separatrix tree is an explicit chain and `Sigma L` is computable;
3. upper semicontinuity bookkeeping across walls (the arm endpoints jump by
   monodromy at wall crossings; needed: `Sigma L` attains its cell-closure
   sup, i.e. no upward jump INTO the open cell).

Item 3 is the honest new gap this reduction isolates; 1 and 2 are structured
special families.

## Relation to the corpus's (A) and the admissibility walls

`CriticalTreeLengthCharge.md` (A) is the ADMISSIBLE-set form
`Sigma_{c in A} L(c) <= 2Rm`, `A = {|f(c)| < 1}`, `m = |A|`; its file states
"(A), equivalently (E), remains open and would solve Erdős #1041".  The
all-hub form (AGG) of this draft is the psh-cleaner variant: the admissible
sum has additional walls at `|f(c_k)| = 1` (a hub leaves the sum), while the
all-hub sum has none.  Trade-off: all-hub (AGG) delivers the parent only
through the tie-implication (a minimizing-but-inadmissible hub must be shown
to come with an admissible short partner) OR by summing only over `A` and
handling the exit walls (at an exit wall the sum is lower semicontinuous from
the admissible side — a hub leaving can only DROP the sum, so the cell-closure
sup analysis survives; the wall configs have a hub at level exactly 1).
Both routes should be recorded; the corpus's (A) stays the canonical target.

## The circle stratum: single-object bounds die, the aggregate survives

Probe (400 unimodular configurations, n = 3..7, random / near-gon / clustered
angles, guarded DOP853 instrument):

- the single-arm budget `<= 1` (conjecture UA, briefly entertained) and the
  single-hub budget `<= 2` are REFUTED on the circle stratum: adversarial
  polish reached a single hub with `L = 2.442` at unimodular roots (angles
  approx `(0.29, 1.77, -2.27, -1.00)`-adjacent family, hub value `1.006`);
- the aggregate held at every sample: `max Sigma_c L(c)/(2(n-1) R_MEC)
  = 0.998385`, approached at near-gon configurations; at the single-hub
  violator the aggregate ratio is only `0.682` — compensation is essential
  and generous away from the gon;
- the long hubs are the HIGH hubs: the `2.44` hub has `|f(c)| = 1.006 > 1`
  (inadmissible), and the admissible-set sum of `CriticalTreeLengthCharge.md`
  (A) excludes exactly these (at the violator, `Sigma_A L = 1.65` against
  budget `4`).  Height caps admissible arms; compensation caps the rest.

Reflection identity special to the circle stratum (proved, elementary): for
unimodular roots, `u(1/conj(z)) - u(z) = -Sigma_k log|b_{c_k}(z)| >= 0` inside
the disk (`b_c` = Blaschke factor of the critical point `c`), an exact
interior/exterior comparison available to a future circle-stratum argument.

## Degree-wise certifiability of the terminal strata

After the psh push, the terminal strata at fixed degree `n` are compact
finite-dimensional real families: the full circle stratum is `n` angles mod
rotation (`n-1` real parameters; `4` at `n = 5`), and each wall/spine lock
removes further dimensions.  For a FIXED degree, (AGG) on the terminal strata
is therefore a certified-computation-sized problem (interval arithmetic over a
compact low-dimensional family), while the psh reduction handles the interior.
This is a concrete path to closing NEW DEGREES (n = 5 first) end to end:
psh interior push + certified terminal-strata verification + the already-
landed Corollary G / Theorem L / Corollary S wiring.

## Evidence so far

- n=3 adversarial polish of `Sigma L/(4 R_MEC)`: sup `0.9978`, extremal
  converged to the equilateral (radial) family with critical-value tie
  `2e-4`; guarded instrument excludes the exact degenerate stratum where the
  ratio is exactly 1 (asserted from the ordinary proof).
- n=4: killer witness gives `5.905/6.006 = 0.983`; sweep pending.
- n=4 sweep (guarded instrument): best ratio `0.875` before polish; the two
  stored degree-4 witnesses above are the known-hardest degree-4 points and
  sit at `0.983` and `0.959`.

## ADDENDUM (same day; supersedes the conjectural status above): (AGG) IS REFUTED; the algebraic half survives

The adversarial fleet closed the question hours after the sections above were
written.  **(AGG-MEC) is FALSE at n = 4**, and with it the corpus's
admissible-set aggregate — the sections above stand as reduction machinery
and evidence record; the conjectural row itself is dead.

Witness (closed unit disk, MEC = unit circle exactly, ray-separated per
`AttachmentAwareReeb.md` Theorem 1, saddle separations `>= 4.0e-2`, ALL
THREE HUBS ADMISSIBLE, `|f(c_k)| = 0.99683..0.99684`):

```text
roots:  0.9983958848690963 - 0.0006084363263325 i
       -0.0001473349861452 + 0.9999999891462010 i
       -0.9984325248818108 + 0.0004538173765221 i
        0.0001473349861452 - 0.9999999891462010 i
per-hub L: 1.954108390, 2.011510158, 2.040733609   (TWO hubs over 2)
Sigma_c L(c) = 6.006352157  >  6 = 2 R_MEC (n-1);   ratio = 1.001058693
```

Certification: five independent ODE solvers agreeing to `6e-10`; a FLOW-FREE
inscribed polyline (fibre vertices from `np.roots`, no integrator at all)
gives `>= 6.006306968`, i.e. `ratio >= 1.001051` independently of every flow
instrument; this session's own DOP853 engine reproduces `6.006352157` as a
sixth instrument.  Shrinking into the open disk preserves everything
(similarity invariance).  The violating set is open (second witness
`1.000882`; stable under `1e-6` perturbation).

Refuted at once by the same witness: `CriticalTreeLengthCharge.md` (A)
(all hubs admissible, `m = 3`: `6.00635 <= 6` false), equivalently (E) and
componentwise (F); `AdmissibleCriticalArcProductLab.md` (AQ) (measured
`1.001853`) and (CAQ); and the AGGREGATE form of the open producer
`critical_point_selection_with_inverse_ray_length_control`.  Surviving: the
SELECTION form — `min_c L(c)/(2R) = 0.977054` at the witness (the Result-C
redirect of `MinimalHubArmBudgetRefutation.md`, enforced a third time).
Degree boundary: `n = 3` unrefuted (two independent hunts stall at
`0.999386`); **`n = 5` also refuted at one certified witness** (perturbed
regular pentagon, all four hubs admissible at `0.99939`, `Sigma = 8.002702 >
8`, ratio `1.000338`, flow-free polyline `>= 1.000337`, `S = 0.999877`,
min-hub `0.9640`; caveat: a single witness, not a demonstrated open region —
the `1e-6` perturbation probe crosses a tie locus and drops to `0.985`, and
the witness sits exactly at the `value_gap = 1e-9` gate boundary, the
thinnest accepted measurement).  Working conjecture: (AGG) holds at `n = 3`
and fails for every `n >= 4`.

Mechanism and instrument law: the witness is a slightly asymmetrised
near-square `(z^2 - a^2)(z^2 + b^2)`; the symmetric member has all critical
values on one ray — a NEWTON SADDLE CONNECTION — and breaking the symmetry
lets one arm squeeze past a foreign saddle.  The binding degeneracy is a
foreign critical VALUE near the descending segment `[0, f(c)]`, invisible to
critical-POINT separation gates:

```text
value_gap := min_{i != j} dist( f(c_j), segment [0, f(c_i)] ) / |f(c_i)|
```

An apparent violation AT `value_gap = 1.2e-16` was adjudicated FAKE (solver
disagreement `4.1e-2`, collapses off-locus); the true witnesses sit at
`value_gap ~ 1e-9` with all instruments agreeing.  Every future arm
measurement near ties should carry this gate.

Exact factorisation localising the failure (proved): `AGG ratio = S * V`,
with `S = (Sigma_c |f(c)|^{1/n})/(R(n-1))` pure algebra and
`V = (Sigma_c L(c))/(2 Sigma_c |f(c)|^{1/n})` the metric half (the
straightening `F = f^{1/n}` maps the separatrix tree onto radial segments of
total `F`-length `2 Sigma_c |f(c)|^{1/n}`).  At the witness `S = 0.99921 < 1`
while `V = 1.00185 > 1`: the violation is ENTIRELY metric; near the radial
family `1 - S = Theta(d^4)` vs `1 - AGG = Theta(d)`.

**The surviving algebraic aggregate — conjecture (S):**

```text
Sigma_{k=1}^{n-1} |f(c_k)|^{1/n}  <=  (n-1) R
```

— the ARITHMETIC mean of the merge-level capacities is at most the
circumradius, strictly strengthening Schur–Fekete (geometric mean `<= R`),
tight on the radial family, PROVED for `n = 2, 3, 4, 5`.  The all-degree
bridge in `FreePointTorusPshReduction.md` proves
`FP_{n-1} ==> (S)_n` by the psh root-polydisk maximum principle, the
self-inversive torus identity
`|f(c)| = prod_k |1 - conj(c) c_k|` for unimodular roots, and the exact
concavity exponent conversion.  It consumes the landed `FP_3` and `FP_4`
theorems for the two new degrees.  The assertion is unrefuted anywhere
(adversarial sup exactly
`1.000000` at `n <= 13`; `S = 0.99921` at the (AGG) witness).  Supporting
exact structure (proved; novelty NOT established, assume classical until
searched): the coarea identity `Sigma_k |f(c_k)|^{1/n} =
int_0^inf (nu(lambda^n) - 1) d lambda`, and the sharp critical-value bound
`|f(c)| <= (2/n)^n (n-1)^{n-1} R^n` with equality at `(z-a)(z-b)^{n-1}`.
(S) does not imply the parent by itself; `FP_m` remains open for `m>=5`,
and the parent carrier remains hub
SELECTION (`min_c L(c) < 2`), for which the psh machinery and terminal-strata
taxonomy above remain the live program.
