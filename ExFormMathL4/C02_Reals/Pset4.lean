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

variable (a b c d x y ε : ℝ)
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

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    |x| < y ↔ -y < x ∧ x < y
-- ---------------------------------------------------------------------

-- Proof 1
example : |x| < y ↔ -y < x ∧ x < y := by
  exact abs_lt

-- Proof 2
example : |x| < y ↔ -y < x ∧ x < y :=
  abs_lt

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that if `0 < ε` then `0 < ε/2`.
-- ---------------------------------------------------------------------

-- Proof 1
example
  (hε : 0 < ε)
  : 0 < ε / 2 :=
by
  exact half_pos hε

-- Proof 2
example
  (hε : 0 < ε)
  : 0 < ε / 2 :=
half_pos hε

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that if `a < x` and `b < y` then `a + b < x + y`.
-- ---------------------------------------------------------------------

-- Proof 1
example
  (h1 : a < x)
  (h2 : b < y)
  : a + b < x + y :=
by
  exact add_lt_add h1 h2

-- Proof 2
example
  (h1 : a < x)
  (h2 : b < y)
  : a + b < x + y :=
add_lt_add h1 h2

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that if `0 < ε` then `0 < ε/3`.
-- ---------------------------------------------------------------------

-- Proof 1
example
  (hε : 0 < ε)
  : 0 < ε / 3 :=
by
  linarith

-- Proof 2
example
  (hε : 0 < ε)
  : 0 < ε / 3 :=
by
  simp [hε]

-- ---------------------------------------------------------------------
-- Exercise 8. Prove that if `a + c < x` and `b + d < y` then
-- `a + b + c + d < x + y`.
-- ---------------------------------------------------------------------

-- Proof 1
example
  (h1 : a + c < x)
  (h2 : b + d < y)
  : a + b + c + d < x + y :=
by
  linarith
