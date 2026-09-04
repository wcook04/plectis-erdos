# Z85_1: Stern--Brocot run geometry: direction-flip involution and unit-run height recursion

[All problems and zones](BROWSER.md)

<a id="node-2696071d9ee76693"></a>
## direction_flip_exchanges_left_and_right_and_is_an_involution

PROVED TWO-DIRECTION INVOLUTION: LR.left.flip is LR.right, LR.right.flip is LR.left, and for every Stern--Brocot direction d, applying flip twice returns d.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The three equalities concern only the direction labels. They do not prove that flipping a whole word swaps its coordinates, preserves a tree measure or run mass, or produces any arithmetic or irrationality consequence.

- Lean declaration: [LR.flip_left](../../Erdos249257/SternBrocotRunGeometry.lean#L47)
- Lean declaration: [LR.flip_right](../../Erdos249257/SternBrocotRunGeometry.lean#L48)
- Lean declaration: [LR.flip_flip](../../Erdos249257/SternBrocotRunGeometry.lean#L49)

- incoming **complements**: [Z85::prepending_one_run_adds_the_previous_first_boundary_coordinate_to_height](BROWSER_Z85_1.md#node-8d97808d599d65fb). The flip laws normalize alternation of left and right direction labels, while the unit-run recursion records the corresponding direction-free continuant height update; neither theorem derives the other.

<a id="node-8d97808d599d65fb"></a>
## prepending_one_run_adds_the_previous_first_boundary_coordinate_to_height

PROVED UNIT-RUN RECURSION: for every list of run lengths ns, runHeight (1 :: ns) equals runHeight ns plus the first coordinate of runBoundaryPair ns.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is one exact recursion identity. It supplies no lower bound by itself, does not state the replicated-unit Fibonacci formula or the later defect expansion, and says nothing about run-tail mass after denominator clearing or irrationality of the totient series.

- Lean declaration: [runHeight_one_cons](../../Erdos249257/SternBrocotRunGeometry.lean#L385)

- outgoing **complements**: [Z85::direction_flip_exchanges_left_and_right_and_is_an_involution](BROWSER_Z85_1.md#node-2696071d9ee76693). The flip laws normalize alternation of left and right direction labels, while the unit-run recursion records the corresponding direction-free continuant height update; neither theorem derives the other.

