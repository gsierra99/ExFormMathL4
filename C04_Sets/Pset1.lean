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

example : A ⊆ A := by
  rw [subset_def]
  intro x hx
  exact hx

example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro hAsB hBsC
  rw [subset_def] at *
  intro x hxeA
  apply hAsB at hxeA
  apply hBsC at hxeA
  exact hxeA

example : A ⊆ A ∪ B := by
  rw [subset_def]
  intro x hxeA
  rw [mem_union_iff]
  left
  exact hxeA

example : A ∩ B ⊆ A := by
  rw [subset_def]
  intro x h_x_in_AyB
  rw [mem_inter_iff] at h_x_in_AyB
  cases' h_x_in_AyB with hA hB
  exact hA

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
