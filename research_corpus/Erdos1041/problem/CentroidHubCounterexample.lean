import Mathlib

/-!
# Erdős #1041: exact centroid-spoke counterexample

This module represents Gaussian rationals as pairs and independently checks
the exact certificate from `CentroidHubCounterexample.md`.  Four named points
on four different centroid spokes have squared quintic modulus greater than
`1 + 1/5000`, although all roots lie strictly in the unit disk and every pair
has squared separation greater than the stronger `5/9` close-pair certificate.
-/

namespace ErdosProblems.Erdos1041

abbrev GaussianRat := ℚ × ℚ

def grAdd (a b : GaussianRat) : GaussianRat :=
  (a.1 + b.1, a.2 + b.2)

def grSub (a b : GaussianRat) : GaussianRat :=
  (a.1 - b.1, a.2 - b.2)

def grMul (a b : GaussianRat) : GaussianRat :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def grScale (q : ℚ) (a : GaussianRat) : GaussianRat :=
  (q * a.1, q * a.2)

def grNormSq (a : GaussianRat) : ℚ :=
  a.1 ^ 2 + a.2 ^ 2

def rationalCirclePoint (s : ℚ) : GaussianRat :=
  ((1 - s ^ 2) / (1 + s ^ 2), 2 * s / (1 + s ^ 2))

def centroidWitnessDirections : Fin 5 → GaussianRat :=
  ![rationalCirclePoint 0,
    rationalCirclePoint (5 / 8),
    rationalCirclePoint (7 / 2),
    rationalCirclePoint (-(11 / 3)),
    rationalCirclePoint (-(5 / 7))]

def centroidWitnessRadius : ℚ := 99999 / 100000

def centroidWitnessRoots (j : Fin 5) : GaussianRat :=
  grScale centroidWitnessRadius (centroidWitnessDirections j)

def centroidWitnessCentroid : GaussianRat :=
  grScale (1 / 5)
    (grAdd (centroidWitnessRoots 0)
      (grAdd (centroidWitnessRoots 1)
        (grAdd (centroidWitnessRoots 2)
          (grAdd (centroidWitnessRoots 3) (centroidWitnessRoots 4)))))

def centroidWitnessSpokePoint (j : Fin 5) (t : ℚ) : GaussianRat :=
  grAdd centroidWitnessCentroid
    (grScale t (grSub (centroidWitnessRoots j) centroidWitnessCentroid))

def centroidWitnessPolynomialValue (z : GaussianRat) : GaussianRat :=
  grMul (grSub z (centroidWitnessRoots 0))
    (grMul (grSub z (centroidWitnessRoots 1))
      (grMul (grSub z (centroidWitnessRoots 2))
        (grMul (grSub z (centroidWitnessRoots 3))
          (grSub z (centroidWitnessRoots 4)))))

def centroidWitnessSpokeValueSq (j : Fin 5) (t : ℚ) : ℚ :=
  grNormSq (centroidWitnessPolynomialValue (centroidWitnessSpokePoint j t))

/-- The five parametrized directions lie exactly on the rational unit circle. -/
theorem centroidWitnessDirections_unit :
    ∀ j, grNormSq (centroidWitnessDirections j) = 1 := by
  decide +kernel

/-- Every scaled witness root lies strictly inside the unit disk. -/
theorem centroidWitnessRoots_inside :
    ∀ j, grNormSq (centroidWitnessRoots j) < 1 := by
  decide +kernel

/-- The witness remains in the separated branch of the refined quintic
close-pair theorem. -/
theorem centroidWitness_pairwiseSeparated :
    ∀ i j, i ≠ j →
      (5 : ℚ) / 9 < grNormSq (grSub (centroidWitnessRoots i) (centroidWitnessRoots j)) := by
  decide +kernel

/-- Four exact rational waypoints certify escape on four distinct centroid
spokes.  Consequently at most one complete centroid spoke can be safe. -/
theorem centroidWitness_four_spokes_escape :
    (1 : ℚ) + 1 / 5000 < centroidWitnessSpokeValueSq 1 (23 / 100) ∧
    (1 : ℚ) + 1 / 5000 < centroidWitnessSpokeValueSq 2 (1 / 4) ∧
    (1 : ℚ) + 1 / 5000 < centroidWitnessSpokeValueSq 3 (1 / 8) ∧
    (1 : ℚ) + 1 / 5000 < centroidWitnessSpokeValueSq 4 (3 / 10) := by
  decide +kernel

end ErdosProblems.Erdos1041
