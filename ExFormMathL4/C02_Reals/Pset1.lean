-- C02_Reals/Pset1.lean
-- Problem set 1: Equalities and inequalities between numerical expressions.
-- Gabriel Sierra Gallego.
-- Seville, October 27, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with basic equalities and
-- inequalities between numerical expressions in Lean4.
--
-- It is based on [Section01logic/Sheet4.lean](https://tinyurl.com/288azgyn)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    2 + 2 = 4
-- ---------------------------------------------------------------------

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
