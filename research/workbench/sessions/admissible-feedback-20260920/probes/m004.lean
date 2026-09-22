import ErdosProblems.Synthesis.FeedbackContinuation
open ErdosProblems.Synthesis.FeedbackContinuation
namespace FeedbackTrace_free
theorem step_0 : Admissible 8 2 0 3
    (1 / 2 : ℝ) (1 / 1 : ℝ) (3 / 1 : ℝ) (4 / 1 : ℝ) := by
  norm_num [Admissible]
theorem step_1 : Admissible 8 2 2 6
    (1 / 4 : ℝ) (1 / 2 : ℝ) (3 / 2 : ℝ) (3 / 1 : ℝ) := by
  norm_num [Admissible]
theorem step_2 : Admissible 8 2 8 6
    (1 / 8 : ℝ) (1 / 4 : ℝ) (3 / 4 : ℝ) (3 / 2 : ℝ) := by
  norm_num [Admissible]
theorem step_3 : Admissible 8 2 14 6
    (1 / 16 : ℝ) (1 / 8 : ℝ) (3 / 8 : ℝ) (3 / 4 : ℝ) := by
  norm_num [Admissible]
theorem step_4 : Admissible 8 2 20 6
    (1 / 32 : ℝ) (1 / 16 : ℝ) (3 / 16 : ℝ) (3 / 8 : ℝ) := by
  norm_num [Admissible]
theorem step_5 : Admissible 8 2 26 6
    (1 / 64 : ℝ) (1 / 32 : ℝ) (3 / 32 : ℝ) (3 / 16 : ℝ) := by
  norm_num [Admissible]
theorem step_6 : Admissible 8 2 32 6
    (1 / 128 : ℝ) (1 / 64 : ℝ) (3 / 64 : ℝ) (3 / 32 : ℝ) := by
  norm_num [Admissible]
theorem step_7 : Admissible 8 2 38 8
    (1 / 256 : ℝ) (1 / 128 : ℝ) (3 / 128 : ℝ) (3 / 64 : ℝ) := by
  norm_num [Admissible]
end FeedbackTrace_free

open ErdosProblems.Synthesis.FeedbackContinuation
namespace FeedbackTrace_divisor_count
theorem step_0 : Admissible 1 1 0 1
    (1 / 2 : ℝ) (0 / 1 : ℝ) (3 / 2 : ℝ) (1 / 1 : ℝ) := by
  norm_num [Admissible]
example : (1 : ℕ) = 1 := by norm_num
theorem step_1 : Admissible 2 1 1 1
    (1 / 4 : ℝ) (0 / 1 : ℝ) (1 / 1 : ℝ) (1 / 2 : ℝ) := by
  norm_num [Admissible]
example : (1 : ℕ) = 1 + 0 := by norm_num
theorem step_2 : Admissible 3 1 2 1
    (1 / 8 : ℝ) (0 / 1 : ℝ) (5 / 8 : ℝ) (1 / 4 : ℝ) := by
  norm_num [Admissible]
example : (1 : ℕ) = 1 + 0 := by norm_num
theorem step_3 : Admissible 4 1 3 1
    (1 / 16 : ℝ) (0 / 1 : ℝ) (3 / 8 : ℝ) (1 / 8 : ℝ) := by
  norm_num [Admissible]
example : (1 : ℕ) = 1 + 0 + 0 := by norm_num
theorem step_4 : Admissible 5 1 4 1
    (1 / 32 : ℝ) (0 / 1 : ℝ) (7 / 32 : ℝ) (1 / 16 : ℝ) := by
  norm_num [Admissible]
example : (1 : ℕ) = 1 + 0 := by norm_num
theorem step_5 : Admissible 6 1 5 1
    (1 / 64 : ℝ) (0 / 1 : ℝ) (1 / 8 : ℝ) (1 / 32 : ℝ) := by
  norm_num [Admissible]
example : (1 : ℕ) = 1 + 0 + 0 + 0 := by norm_num
theorem step_6 : Admissible 7 1 6 1
    (1 / 128 : ℝ) (0 / 1 : ℝ) (9 / 128 : ℝ) (1 / 64 : ℝ) := by
  norm_num [Admissible]
example : (1 : ℕ) = 1 + 0 := by norm_num
theorem step_7 : Admissible 8 1 7 2
    (1 / 256 : ℝ) (0 / 1 : ℝ) (5 / 128 : ℝ) (1 / 128 : ℝ) := by
  norm_num [Admissible]
example : (2 : ℕ) = 1 + 0 + 0 + 1 := by norm_num
end FeedbackTrace_divisor_count
