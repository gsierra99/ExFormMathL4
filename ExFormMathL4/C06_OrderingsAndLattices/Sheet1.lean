-- C06_OrderingsAndLattices/Pset1.lean
-- Problem set 1
-- Gabriel Sierra Gallego.
-- Seville, November 05, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study basic results about partial orders
--
-- It is based on [Section06OrderingsAndLattices/Sheet1.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic


variable (X : Type) [PartialOrder X]


example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc


example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  trans b
  · exact hab
  · exact hbc


variable (a b c d : X)


example : a ≤ a := by
  exact Preorder.le_refl a


example (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  exact le_implies_le_of_le_of_le hab hcd hbc

---------------------------------------------------------------------

example (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = b := by
  have hba : b ≤ a := by exact Preorder.le_trans b c a hbc hca
  exact le_antisymm hab hba


example (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = b := by
  apply le_antisymm hab
  exact le_trans hbc hca
