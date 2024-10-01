import Mathlib.Tactic

variable (X : Type)
variable (A B C D E : Set X)
variable (x y z : X)

theorem subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := by
  rfl

variable (x : X)

theorem mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  rfl

theorem mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
  Iff.rfl

open Set

example : A ∪ A = A := by
  ext x
  constructor
  intro hx
  rw [mem_union_iff] at hx
  cases' hx with hxl hxr
  exact hxl
  exact hxr
  intro hx
  rw [mem_union_iff]
  left
  exact hx

example : A ∩ A = A := by
  ext x
  constructor
  intro hx
  rw [_root_.mem_inter_iff] at hx
  cases' hx with hxl hxr
  exact hxl
  intro hx
  rw [_root_.mem_inter_iff]
  exact ⟨hx, hx⟩

example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  intro hx
  rw [_root_.mem_inter_iff] at hx
  cases' hx with hxl hxr
  exact hxr
  intro hx
  rw [_root_.mem_inter_iff]
  constructor
  exfalso
  cases hx
  exact hx

example : A ∪ univ = univ := by
  ext x
  constructor
  intro hx
  rw [mem_union_iff] at hx
  cases' hx with hl hr
  exact trivial
  exact hr
  intro hx
  rw [mem_union_iff]
  right
  exact hx

example : A ⊆ B → B ⊆ A → A = B := by
  intro hAB hBA
  ext x
  rw [_root_.subset_def] at hAB hBA
  constructor
  intro hx
  apply hAB at hx
  exact hx
  intro hx
  apply hBA at hx
  exact hx

example : A ∩ B = B ∩ A := by
  ext x
  constructor
  intro hx
  rw [_root_.mem_inter_iff] at *
  cases' hx with hxA hxB
  constructor
  exact hxB
  exact hxA
  intro hx
  rw [_root_.mem_inter_iff] at *
  cases' hx with hxB hxA
  constructor
  exact hxA
  exact hxB

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  constructor
  intro hx
  rw [_root_.mem_inter_iff] at *
  cases' hx with hxl hxr
  rw [_root_.mem_inter_iff] at hxr
  cases' hxr with hxrl hxrr
  constructor
  rw [_root_.mem_inter_iff]
  exact ⟨hxl, hxrl⟩
  exact hxrr
  intro hx
  rw [_root_.mem_inter_iff] at *
  cases' hx with hxl hxr
  rw [_root_.mem_inter_iff] at hxl
  cases' hxl with hxll hxlr
  constructor
  exact hxll
  rw [_root_.mem_inter_iff]
  exact ⟨hxlr, hxr⟩

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  intro hx
  rw [mem_union_iff] at *
  cases' hx with hxl hxr
  left
  rw [mem_union_iff]
  left
  exact hxl
  rw [mem_union_iff] at hxr
  cases' hxr with hxrl hxrr
  left
  rw [mem_union_iff]
  right
  exact hxrl
  right
  exact hxrr
  intro hx
  rw [mem_union_iff] at *
  cases' hx with hxl hxr
  rw [mem_union_iff] at hxl
  cases' hxl with hxll hxlr
  left
  exact hxll
  right
  rw [mem_union_iff]
  left
  exact hxlr
  right
  rw [mem_union_iff]
  right
  exact hxr

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  intro hx
  rw [mem_union_iff] at hx
  cases' hx with hxl hxr
  rw [_root_.mem_inter_iff]
  constructor
  rw [mem_union_iff]
  left
  exact hxl
  rw [mem_union_iff]
  left
  exact hxl
  rw [_root_.mem_inter_iff] at hxr
  cases' hxr with hxrl hxrr
  rw [_root_.mem_inter_iff]
  constructor
  rw [mem_union_iff]
  right
  exact hxrl
  rw [mem_union_iff]
  right
  exact hxrr
  intro hx
  rw [_root_.mem_inter_iff] at hx
  rw [mem_union_iff]
  cases' hx with hxl hxr
  rw [mem_union_iff] at hxl hxr
  cases' hxl with hxll hxlr
  left
  exact hxll
  cases' hxr with hxrl hxrr
  left
  exact hxrl
  right
  rw [_root_.mem_inter_iff]
  exact ⟨hxlr, hxrr⟩

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  constructor
  intro hx
  rw [_root_.mem_inter_iff] at hx
  cases' hx with hxl hxr
  rw [mem_union_iff] at hxr
  rw [mem_union_iff]
  cases' hxr with hxrl hxrr
  left
  exact mem_inter hxl hxrl
  right
  exact mem_inter hxl hxrr
  intro hx
  rw [mem_union_iff] at hx
  rw [_root_.mem_inter_iff]
  cases' hx with hxl hxr
  constructor
  rw [_root_.mem_inter_iff] at hxl
  cases' hxl with hxll hxlr
  exact hxll
  rw [mem_union_iff]
  rw [_root_.mem_inter_iff] at hxl
  cases' hxl with hxll hxlr
  left
  exact hxlr
  rw [_root_.mem_inter_iff] at hxr
  cases' hxr with hxrl hxrr
  constructor
  exact hxrl
  rw [mem_union_iff]
  right
  exact hxrr
