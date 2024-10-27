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

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    2 + 2 ≠ 5
-- ---------------------------------------------------------------------

example : (2 : ℝ) + 2 ≠ 5 := by
  norm_num

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    2 + 2 < 5
-- ---------------------------------------------------------------------

example : (2 : ℝ) + 2 < 5 := by
  norm_num

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    (∃ x ∈ ℝ)[3x + 7 = 12]
-- ---------------------------------------------------------------------

-- Proof 1
example : ∃ x : ℝ, 3 * x + 7 = 12 := by
  use 5/3
  -- ⊢ 3 * (5 / 3) + 7 = 12
  norm_num

-- Proof 2
example : ∃ x : ℝ, 3 * x + 7 = 12 :=
  ⟨5/3, by norm_num⟩

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    (∃ x ∈ ℝ)[3x + 7 ≠ 12]
-- ---------------------------------------------------------------------

-- Proof 1
example : ∃ x : ℝ, 3 * x + 7 ≠ 12 := by
  use 1
  -- ⊢ 3 * 1 + 7 ≠ 12
  norm_num

-- Proof 2
example : ∃ x : ℝ, 3 * x + 7 ≠ 12 :=
  ⟨1, by norm_num⟩

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    (∃ x, y ∈ ℝ)[2x + 3y = 7 ∧ x + 2y = 4]
-- ---------------------------------------------------------------------

-- Proof 1
example : ∃ x y : ℝ, 2 * x + 3 * y = 7 ∧ x + 2 * y = 4 := by
  use 2, 1
  -- ⊢ 2 * 2 + 3 * 1 = 7 ∧ 2 + 2 * 1 = 4
  norm_num

-- Proof 2
example : ∃ x y : ℝ, 2 * x + 3 * y = 7 ∧ x + 2 * y = 4 :=
  ⟨2, 1, by norm_num⟩
