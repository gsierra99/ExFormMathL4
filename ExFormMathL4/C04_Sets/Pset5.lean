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

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    A ∪ A = A
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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


-- Proof 2 (automatic)
example : A ∪ A = A := by
  exact union_eq_self_of_subset_left fun ⦃a⦄ a => a

-- Proof 3 (equilibrated)
example : A ∪ A = A := by
  simp

-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    A ∩ A = A
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ∩ A = A := by
  exact inter_eq_self_of_subset_right fun ⦃a⦄ a => a

-- Proof 3 (equilibrated)
example : A ∩ A = A := by
  simp

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    A ∩ ∅ = ∅
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ∩ ∅ = ∅ := by
  exact inter_empty A

-- Proof 3 (equilibrated)
example : A ∩ ∅ = ∅ := by
  simp

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    A ∪ univ = univ
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ∪ univ = univ := by
  exact union_univ A

-- Proof 3 (equilibrated)
example : A ∪ univ = univ := by
  simp

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    A ⊆ B → B ⊆ A → A = B
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ⊆ B → B ⊆ A → A = B := by
  exact fun a a_1 => Subset.antisymm a a_1

-- Proof 3 (equilibrated)
example : A ⊆ B → B ⊆ A → A = B := by
  intro hAB hBA
  exact Subset.antisymm hAB hBA

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    A ∩ B = B ∩ A
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ∩ B = B ∩ A := by
  exact inter_comm A B

-- Proof 3 (equilibrated)
example : A ∩ B = B ∩ A := by
  ext x
  simp
  exact And.comm

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    A ∩ (B ∩ C) = A ∩ B ∩ C
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  exact Eq.symm (inter_assoc A B C)

-- Proof 3 (equilibrated)
example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  simp
  exact Iff.symm and_assoc

-- ---------------------------------------------------------------------
-- Exercise 8. Prove that
--    A ∪ (B ∪ C) = A ∪ B ∪ C
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  exact Eq.symm (union_assoc A B C)

-- Proof 3 (equilibrated)
example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  simp
  exact Iff.symm or_assoc

-- ---------------------------------------------------------------------
-- Exercise 9. Prove that
--    A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C)
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  exact union_inter_distrib_left A B C

-- Proof 3 (equilibrated)
example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  simp
  exact or_and_left

-- ---------------------------------------------------------------------
-- Exercise 10. Prove that
--    A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
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

-- Proof 2 (automatic)
example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  exact inter_union_distrib_left A B C

-- Proof 3 (equilibrated)
example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  simp
  exact and_or_left
