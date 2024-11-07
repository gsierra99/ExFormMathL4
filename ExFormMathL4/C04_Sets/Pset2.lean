-- C04_Sets/Pset2.lean
-- Problem set 2
-- Gabriel Sierra Gallego.
-- Seville, November 03, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study results about the universal set and the empty set
--
-- It is based on [Section04functions/Sheet2.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

open Set

variable (X : Type)
variable (A B C D E : Set X)
variable (x y z : X)

open Set

example : x ∈ (univ : Set X) := by
  trivial

example : x ∈ (∅ : Set X) → False := by
  intro h
  cases h

example : A ⊆ univ := by
  rw [subset_def]
  intro x _hxA
  trivial

example : ∅ ⊆ A := by
  rw [subset_def]
  intro x hx
  cases hx
