import Mathlib.Tactic

example : (2 : ℝ) + 2 = 4 := by
  norm_num

example : (2 : ℝ) + 2 ≠ 5 := by
  norm_num

example : (2 : ℝ) + 2 < 5 := by
  norm_num

example : ∃ x : ℝ, 3 * x + 7 = 12 := by
  use 5/3
  norm_num

example : ∃ x : ℝ, 3 * x + 7 ≠ 12 := by
  use 1
  norm_num

example : ∃ x y : ℝ, 2 * x + 3 * y = 7 ∧ x + 2 * y = 4 := by
  use 2, 1
  norm_num
