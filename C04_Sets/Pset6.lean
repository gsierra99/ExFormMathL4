import Mathlib.Tactic -- imports all the Lean tactics

theorem mem_def (X : Type) (P : X → Prop) (a : X) :
    a ∈ {x : X | P x} ↔ P a := by
  rfl

open Set

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)
variable (A B C D E : Set X)
variable (x y z : X)


theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

variable (x : X)

theorem mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

theorem mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  Iff.rfl

example : S ⊆ f ⁻¹' (f '' S) := by
  rw [Set.subset_def]
  intro x hx
  rw [preimage]
  rw [image]
  rw [Set.mem_def]
  sorry

example : f '' (f ⁻¹' T) ⊆ T := by
  sorry

example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  sorry

example : id ⁻¹' S = S := by
  sorry

example : id '' S = S := by
  sorry

variable (Z : Type) (g : Y → Z) (U : Set Z)

example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  sorry

example : g ∘ f '' S = g '' (f '' S) := by
  sorry

example (f : ℕ → ℕ) (h : ∀ x, f x = 37) : False :=
  sorry
