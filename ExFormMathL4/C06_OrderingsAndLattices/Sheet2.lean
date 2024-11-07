-- C06_OrderingsAndLattices/Pset2.lean
-- Problem set 2
-- Gabriel Sierra Gallego.
-- Seville, November 05, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study basic results lattices
--
-- It is based on [Section06OrderingsAndLattices/Sheet2.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic


variable (L : Type) [Lattice L] (a b c : L)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    a ⊔ b = b ⊔ a
-- ---------------------------------------------------------------------

-- Proof 1
example : a ⊔ b = b ⊔ a := by
  exact sup_comm a b

-- Proof 2
example : a ⊔ b = b ⊔ a :=
  by
  apply le_antisymm
  · exact sup_le le_sup_right le_sup_left
  · exact sup_le le_sup_right le_sup_left


-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-- ---------------------------------------------------------------------

-- Proof 1
example : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  exact sup_assoc a b c

-- Proof 2
example : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  · apply sup_le (sup_le _ _)
    · trans b ⊔ c
      · exact le_sup_right
      · exact le_sup_right
    · exact le_sup_left
    · trans b ⊔ c
      · exact le_sup_left
      · exact le_sup_right
  · refine' sup_le _ (sup_le _ _)
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right


-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    b ≤ c ⊢  a ⊓ b ≤ a ⊓ c
-- ---------------------------------------------------------------------

-- Proof 1
example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := by
  exact inf_le_inf_left a h

-- Proof 2
example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c := by
  apply le_inf
  · exact inf_le_left
  · trans b
    · exact inf_le_right
    · exact h

-- Proof 3
example (h : b ≤ c) : a ⊓ b ≤ a ⊓ c :=
  le_inf inf_le_left <| le_trans inf_le_right h


-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)
-- ---------------------------------------------------------------------

-- Proof 1
example : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by
  exact le_inf_sup

-- Proof 2
example : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) := by
  apply sup_le
  · apply inf_le_inf_left
    exact le_sup_left
  · apply inf_le_inf_left
    exact le_sup_right


-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c)
-- ---------------------------------------------------------------------

-- Proof 1
example : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) := by
  exact sup_inf_le

-- Proof 2
example : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_inf
  · apply sup_le_sup_left
    exact inf_le_left
  · apply sup_le_sup_left
    exact inf_le_right
