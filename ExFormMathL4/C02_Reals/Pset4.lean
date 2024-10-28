-- C02_Reals/Pset4.lean
-- Problem set 4: The `linarith` tactic.
-- Gabriel Sierra Gallego.
-- Seville, October 28, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we will use the tactics linarith and
-- exact? to search for lemmas.
--
-- It is based on [Section02reals/Sheet4.lean](https://tinyurl.com/24fb2gzz)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

variable (x y : ℝ)
variable (A B C : ℕ)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    |-x| = |x|
-- ---------------------------------------------------------------------

-- Proof 1
example : |-x| = |x| := by
  exact abs_neg x

-- Proof 2
example : |-x| = |x| :=
  abs_neg x

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    |x - y| = |y - x|
-- ---------------------------------------------------------------------

-- Proof 1
example : |x - y| = |y - x| := by
  exact abs_sub_comm x y

-- Proof 2
example : |x - y| = |y - x| :=
  abs_sub_comm x y

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    |x - y| = |y - x|
-- ---------------------------------------------------------------------

-- Proof 1
example : max A B ≤ C ↔ A ≤ C ∧ B ≤ C := by
  exact Nat.max_le

-- Proof 2
example : max A B ≤ C ↔ A ≤ C ∧ B ≤ C :=
  Nat.max_le

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by
  exact abs_lt

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 := by
  exact half_pos hε

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y := by
  exact add_lt_add h1 h2

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 := by
  linarith

example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) : a + b + c + d < x + y := by
  linarith
