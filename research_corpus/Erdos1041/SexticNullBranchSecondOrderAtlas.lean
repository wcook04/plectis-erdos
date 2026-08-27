import ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector
import ErdosProblems.Erdos1041.SexticCanonicalMixedSlice

/-!
# Erdős #1041: the sextic null-branch second-order atlas

The four square-contact connectors have two optimized second-order offsets.
Their transverse terms are the tetrahedral contact values from the preceding
transverse-selector module, so those terms sum to zero.  The average of the
four complete profiles is strictly below minus three fifths; hence one
connector has that uniform limiting margin for every second-order perturbation.
-/

namespace ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas

noncomputable section

open ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector

abbrev sqrtThree : ℝ :=
  ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree

def qZero : ℝ := (7 + 4 * sqrtThree) / 27
def branchSlope : ℝ := (3 / 2) * qZero * (sqrtThree - 1)
def radiusSlope : ℝ := (21 + 11 * sqrtThree) / 54

def slopeFactor : ℝ := 648 - 378 * sqrtThree
def baseFactor : ℝ := -9963 / 2 + 5751 * sqrtThree / 2
def completedSquareFactor : ℝ := 212139 / 4 - 30618 * sqrtThree

def plusRawProfile (k : ℝ) : ℝ :=
  baseFactor * (k - branchSlope) +
    (slopeFactor * (k - branchSlope)) ^ 2 / 16

def minusRawProfile (k : ℝ) : ℝ :=
  -baseFactor * (k - branchSlope) +
    (slopeFactor * (k + branchSlope)) ^ 2 / 16

def plusOffset : ℝ := -117 + 135 * sqrtThree / 2
def minusOffset : ℝ := -9 + 9 * sqrtThree / 2

def profilePP (p q r : ℝ) : ℝ := plusOffset + contactPP p q r
def profileNP (p q r : ℝ) : ℝ := plusOffset + contactNP p q r
def profileNN (p q r : ℝ) : ℝ := minusOffset + contactNN p q r
def profilePN (p q r : ℝ) : ℝ := minusOffset + contactPN p q r

theorem sqrtThree_sq : sqrtThree ^ 2 = 3 :=
  ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree_sq

theorem sqrtThree_lt_twentySix_div_fifteen :
    sqrtThree < (26 / 15 : ℝ) := by
  have hs0 : 0 ≤ sqrtThree := by
    exact le_of_lt
      ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree_pos
  by_contra h
  have hle : (26 / 15 : ℝ) ≤ sqrtThree := le_of_not_gt h
  nlinarith [sqrtThree_sq]

theorem sqrtThree_lt_ninetySeven_div_fiftySix :
    sqrtThree < (97 / 56 : ℝ) := by
  have hs0 : 0 ≤ sqrtThree := by
    exact le_of_lt
      ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree_pos
  by_contra h
  have hle : (97 / 56 : ℝ) ≤ sqrtThree := le_of_not_gt h
  nlinarith [sqrtThree_sq]

theorem completedSquareFactor_eq :
    completedSquareFactor = (2187 / 4 : ℝ) * (97 - 56 * sqrtThree) := by
  unfold completedSquareFactor
  ring

theorem completedSquareFactor_pos : 0 < completedSquareFactor := by
  rw [completedSquareFactor_eq]
  have hs := sqrtThree_lt_ninetySeven_div_fiftySix
  have hlinear : 0 < 97 - 56 * sqrtThree := by linarith
  exact mul_pos (by norm_num) hlinear

theorem plusRawProfile_complete_square (k : ℝ) :
    plusRawProfile k =
      plusOffset + completedSquareFactor * (k - radiusSlope) ^ 2 := by
  have hs2 := sqrtThree_sq
  have hs3 : sqrtThree ^ 3 = 3 * sqrtThree := by
    calc
      sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
      _ = 3 * sqrtThree := by rw [hs2]
  have hs4 : sqrtThree ^ 4 = 9 := by
    calc
      sqrtThree ^ 4 = (sqrtThree ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [hs2]
      _ = 9 := by norm_num
  have hs5 : sqrtThree ^ 5 = 9 * sqrtThree := by
    calc
      sqrtThree ^ 5 = sqrtThree ^ 4 * sqrtThree := by ring
      _ = 9 * sqrtThree := by rw [hs4]
  have hs6 : sqrtThree ^ 6 = 27 := by
    calc
      sqrtThree ^ 6 = (sqrtThree ^ 2) ^ 3 := by ring
      _ = 3 ^ 3 := by rw [hs2]
      _ = 27 := by norm_num
  unfold plusRawProfile plusOffset completedSquareFactor radiusSlope
    baseFactor slopeFactor branchSlope qZero
  ring_nf
  rw [hs6, hs5, hs4, hs3, hs2]
  ring

theorem minusRawProfile_complete_square (k : ℝ) :
    minusRawProfile k =
      minusOffset + completedSquareFactor * (k + radiusSlope) ^ 2 := by
  have hs2 := sqrtThree_sq
  have hs3 : sqrtThree ^ 3 = 3 * sqrtThree := by
    calc
      sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
      _ = 3 * sqrtThree := by rw [hs2]
  have hs4 : sqrtThree ^ 4 = 9 := by
    calc
      sqrtThree ^ 4 = (sqrtThree ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [hs2]
      _ = 9 := by norm_num
  have hs5 : sqrtThree ^ 5 = 9 * sqrtThree := by
    calc
      sqrtThree ^ 5 = sqrtThree ^ 4 * sqrtThree := by ring
      _ = 9 * sqrtThree := by rw [hs4]
  have hs6 : sqrtThree ^ 6 = 27 := by
    calc
      sqrtThree ^ 6 = (sqrtThree ^ 2) ^ 3 := by ring
      _ = 3 ^ 3 := by rw [hs2]
      _ = 27 := by norm_num
  unfold minusRawProfile minusOffset completedSquareFactor radiusSlope
    baseFactor slopeFactor branchSlope qZero
  ring_nf
  rw [hs6, hs5, hs4, hs3, hs2]
  ring

theorem plusRawProfile_minimized (k : ℝ) :
    plusOffset ≤ plusRawProfile k := by
  rw [plusRawProfile_complete_square]
  exact le_add_of_nonneg_right
    (mul_nonneg (le_of_lt completedSquareFactor_pos) (sq_nonneg _))

theorem minusRawProfile_minimized (k : ℝ) :
    minusOffset ≤ minusRawProfile k := by
  rw [minusRawProfile_complete_square]
  exact le_add_of_nonneg_right
    (mul_nonneg (le_of_lt completedSquareFactor_pos) (sq_nonneg _))

theorem plusRawProfile_at_radiusSlope :
    plusRawProfile radiusSlope = plusOffset := by
  rw [plusRawProfile_complete_square]
  ring

theorem minusRawProfile_at_neg_radiusSlope :
    minusRawProfile (-radiusSlope) = minusOffset := by
  rw [minusRawProfile_complete_square]
  ring

/-- The local maximization of a concave quadratic. -/
theorem localQuadratic_le_completedSquare (x slope constant : ℝ) :
    -4 * x ^ 2 + slope * x + constant ≤
      constant + slope ^ 2 / 16 := by
  nlinarith [sq_nonneg (8 * x - slope)]

theorem profile_sum (p q r : ℝ) :
    profilePP p q r + profileNP p q r +
        profileNN p q r + profilePN p q r =
      4 * (-63 + 36 * sqrtThree) := by
  have hsum := contact_sum_zero p q r
  unfold profilePP profileNP profileNN profilePN plusOffset minusOffset
  linarith

theorem profile_average_lt_neg_threeFifths :
    -63 + 36 * sqrtThree < (-3 / 5 : ℝ) := by
  have hs := sqrtThree_lt_twentySix_div_fifteen
  linarith

/-- Every second-order transverse perturbation is covered by one of the four
optimized square-contact connectors with uniform normalized margin -3/5. -/
theorem secondOrder_four_connector_cover (p q r : ℝ) :
    profilePP p q r ≤ (-3 / 5 : ℝ) ∨
    profileNP p q r ≤ (-3 / 5 : ℝ) ∨
    profileNN p q r ≤ (-3 / 5 : ℝ) ∨
    profilePN p q r ≤ (-3 / 5 : ℝ) := by
  by_contra h
  push Not at h
  rcases h with ⟨hpp, hnp, hnn, hpn⟩
  have hsum := profile_sum p q r
  have havg := profile_average_lt_neg_threeFifths
  linarith

end

end ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas
