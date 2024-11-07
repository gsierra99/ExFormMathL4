/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

variable (L : Type) [CompleteLattice L] (a : L)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    ⊥ ≤ a
-- ---------------------------------------------------------------------

-- Proof 1
example : ⊥ ≤ a := by
  exact OrderBot.bot_le a

-- Proof 2
example : ⊥ ≤ a := by
  rw [← sSup_empty]
  apply sSup_le
  rintro b ⟨⟩


-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    a ≤ ⊥ ↔ a = ⊥
-- ---------------------------------------------------------------------

-- Proof 1
example : a ≤ ⊥ ↔ a = ⊥ := by
  exact le_bot_iff

-- Proof 2
example : a ≤ ⊥ ↔ a = ⊥ := by
  constructor
  · rw [← sSup_empty]
    intro h
    apply le_antisymm h
    apply sSup_le
    rintro _ ⟨⟩
  · rintro rfl
    rfl


-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    a ≤ ⊥ ↔ a = ⊥
-- ---------------------------------------------------------------------

-- Proof 1
example (S T : Set L) : S ⊆ T → sSup S ≤ sSup T := by
  exact fun a => sSup_le_sSup a

-- Proof 2
example (S T : Set L) : S ⊆ T → sSup S ≤ sSup T :=
  by
  intro hST
  apply sSup_le
  intro b hb
  apply le_sSup
  apply hST
  exact hb
