-- C04_Sets/Pset1.lean
-- Problem set 1
-- Gabriel Sierra Gallego.
-- Seville, November 03, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study results about inclusion in sets.
--
-- It is based on [Section04functions/Sheet1.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic -- imports all the Lean tactics

namespace Section4sheet1

variable (X : Type)
variable (A B C D : Set X)

theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

variable (x : X)

theorem mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

theorem mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  Iff.rfl


-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    A ⊆ A
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : A ⊆ A := by
  rw [subset_def]
  intro x hx
  exact hx

-- Proof 2 (automatic)
example : A ⊆ A := by
  exact fun ⦃a⦄ a => a

-- Proof 3 (equilibrated)
example : A ⊆ A := by
  simp [subset_def]

  -- ---------------------------------------------------------------------
  -- Exercise 2. Prove that
  --    A ⊆ B → B ⊆ C → A ⊆ C
  -- ---------------------------------------------------------------------

  -- Proof 1 (detailed)
  example : A ⊆ B → B ⊆ C → A ⊆ C := by
    intro hAsB hBsC
    rw [subset_def] at *
    intro x hxeA
    apply hAsB at hxeA
    apply hBsC at hxeA
    exact hxeA

  -- Proof 2 (automatic)
  example : A ⊆ B → B ⊆ C → A ⊆ C := by
    exact fun a a_1 ⦃a_2⦄ a_3 => a_1 (a a_3)

  -- Proof 3 (equilibrated)
  example : A ⊆ B → B ⊆ C → A ⊆ C := by
    intro hAsB hBsC
    rw [subset_def] at *
    intro x hxeA
    apply hBsC
    apply hAsB
    exact hxeA


  -- ---------------------------------------------------------------------
  -- Exercise 3. Prove that
  --    A ⊆ A ∪ B
  -- ---------------------------------------------------------------------

  -- Proof 1 (detailed)
  example : A ⊆ A ∪ B := by
    rw [subset_def]
    intro x hxeA
    rw [mem_union_iff]
    left
    exact hxeA

  -- Proof 2 (automatic)
  example : A ⊆ A ∪ B := by
    exact Set.subset_union_left

  -- Proof 3 (equilibrated)
  example : A ⊆ A ∪ B := by

    sorry


  -- ---------------------------------------------------------------------
  -- Exercise 4. Prove that
  --    A ∩ B ⊆ A
  -- ---------------------------------------------------------------------

  -- Proof 1 (detailed)
  example : A ∩ B ⊆ A := by
    rw [subset_def]
    intro x h_x_in_AyB
    rw [mem_inter_iff] at h_x_in_AyB
    cases' h_x_in_AyB with hA hB
    exact hA

  -- Proof 2 (automatic)
  example : A ∩ B ⊆ A := by
  exact Set.inter_subset_left

  -- Proof 3 (equilibrated)
  example : A ∩ B ⊆ A := by
    simp [subset_def, mem_inter_iff]
    intro x hxA _hxB
    exact hxA


  -- ---------------------------------------------------------------------
  -- Exercise 5. Prove that
  --    A ⊆ B → A ⊆ C → A ⊆ B ∩ C
  -- ---------------------------------------------------------------------

  -- Proof 1 (detailed)
  example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
    intro h_A_in_B h_A_in_C
    rw [subset_def] at *
    intro x x_in_A
    rw [mem_inter_iff]
    constructor
    apply h_A_in_B at x_in_A
    exact x_in_A
    apply h_A_in_C at x_in_A
    exact x_in_A

  -- Proof 2 (automatic)
  example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
    exact fun a a_1 => Set.subset_inter a a_1

  -- Proof 3 (equilibrated)
  example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
    intro hAsB hAsC
    simp [subset_def, mem_inter_iff] at *
    intro x hxA
    specialize hAsB x hxA
    specialize hAsC x hxA
    exact ⟨hAsB, hAsC⟩


  -- ---------------------------------------------------------------------
  -- Exercise 6. Prove that
  --    B ⊆ A → C ⊆ A → B ∪ C ⊆ A
  -- ---------------------------------------------------------------------

  -- Proof 1 (detailed)
  example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
    intro h_B_in_A h_C_in_A
    rw [subset_def] at *
    intro x h_x_in_B_o_C
    rw [mem_union_iff] at h_x_in_B_o_C
    cases' h_x_in_B_o_C with h_x_in_B h_x_in_C
    apply h_B_in_A at h_x_in_B
    exact h_x_in_B
    apply h_C_in_A at h_x_in_C
    exact h_x_in_C

  -- Proof 2 (automatic)
  example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
    exact fun a a_1 => Set.union_subset a a_1

  -- Proof 3 (equilibrated)
  example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
    intro hBsA hCsA
    simp [subset_def, mem_union_iff] at *
    intro x hxeBoC
    cases' hxeBoC with hxeB hxeC
    apply hBsA
    exact hxeB
    apply hCsA
    exact hxeC


  -- ---------------------------------------------------------------------
  -- Exercise 7. Prove that
  --    A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D
  -- ---------------------------------------------------------------------

  -- Proof 1 (detailed)
  example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := by
    intro hAB hCD
    rw [subset_def] at *
    intro x hxAoC
    rw [mem_union_iff] at *
    cases' hxAoC with hxA hxC
    apply hAB at hxA
    left
    exact hxA
    apply hCD at hxC
    right
    exact hxC

  -- Proof 2 (automatic)
  example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := by
    exact fun a a_1 => Set.union_subset_union a a_1

  -- Proof 3 (equilibrated)
  example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D := by
    intro hAsB hCsD
    simp [subset_def, mem_union_iff] at *
    intro x hxAoC
    specialize hAsB x
    specialize hCsD x
    exact Or.imp hAsB hCsD hxAoC


  -- ---------------------------------------------------------------------
  -- Exercise 8. Prove that
  --    A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D
  -- ---------------------------------------------------------------------

  -- Proof 1 (detailed)
  example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
    intro hAB hCD
    rw [subset_def] at *
    intro x hxinAyC
    rw [mem_inter_iff] at *
    cases' hxinAyC with hxinA hxinC
    apply hAB at hxinA
    apply hCD at hxinC
    constructor
    exact hxinA
    exact hxinC

  -- Proof 2 (automatic)
  example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
    exact fun a a_1 => Set.inter_subset_inter a a_1

  -- Proof 3 (equilibrated)
  example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D := by
    intro hAsB hCsD
    simp [subset_def, mem_inter_iff] at *
    intro x hxA hxC
    exact ⟨hAsB x hxA, hCsD x hxC⟩
