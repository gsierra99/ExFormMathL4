-- C06_OrderingsAndLattices/Pset3.lean
-- Problem set 3
-- Gabriel Sierra Gallego.
-- Seville, November 05, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study a more complex result about lattices.
--
-- It is based on [Section06OrderingsAndLattices/Sheet3.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic


example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
