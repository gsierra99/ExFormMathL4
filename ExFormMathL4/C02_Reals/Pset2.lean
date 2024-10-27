-- C02_Reals/Pset2.lean
-- Problem set 2: Algebra in the real numbers.
-- Gabriel Sierra Gallego.
-- Seville, October 27, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to do algebra in the real numbers.
--
-- It is based on [Section01logic/Sheet4.lean](https://tinyurl.com/25sc8h3b)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    (x + y)² = x² + 2xy + y²
-- ---------------------------------------------------------------------

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    (∀ a, b ∈ ℝ)(∃ x ∈ ℝ)[(a+b)³ = a³ + xa²b + 3ab² + b³
-- ---------------------------------------------------------------------

example : ∀ a b : ℝ, ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  intro a b
  -- a b : ℝ
  -- ⊢ ∃ x, (a + b) ^ 3 = a ^ 3 + x * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3
  use 3
  -- ⊢ (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3
  ring

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    (∃ x ∈ ℝ,)(∀ y ∈ ℝ)[y + y = xy]
-- ---------------------------------------------------------------------

example : ∃ x : ℝ, ∀ y, y + y = x * y := by
  use 2
  -- ⊢ ∀ (y : ℝ), y + y = 2 * y
  intro y
  -- y : ℝ
  -- ⊢ y + y = 2 * y
  ring

example : ∀ x : ℝ, ∃ y, x + y = 2 := by
  intro x
  use 2 - x
  ring

example : ∀ x : ℝ, ∃ y, x + y ≠ 2 := by
  intro x
  use 3 - x
  norm_num
