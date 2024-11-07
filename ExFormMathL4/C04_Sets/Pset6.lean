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


-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    S ⊆ f ⁻¹' (f '' S)
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : S ⊆ f ⁻¹' (f '' S) := by
  rw [Set.subset_def]
  intro x hx
  rw [preimage, image]
  simp
  use x


-- Proof 2 (automatic)
example : S ⊆ f ⁻¹' (f '' S) := by
  exact subset_preimage_image f S

-- Proof 3 (equilibrated)
example : S ⊆ f ⁻¹' (f '' S) := by
  sorry



-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    f '' (f ⁻¹' T) ⊆ T
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : f '' (f ⁻¹' T) ⊆ T := by
  rw [Set.subset_def]
  intro y hy
  simp at hy
  obtain ⟨x, hx, hfx⟩ := hy
  rw [← hfx]
  exact hx

-- Proof 2 (automatic)
example : f '' (f ⁻¹' T) ⊆ T := by
  exact image_preimage_subset f T

-- Proof 3 (equilibrated)
example : f '' (f ⁻¹' T) ⊆ T := by
  sorry


-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    f '' S ⊆ T ↔ S ⊆ f ⁻¹' T
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  intro h
  rw [Set.subset_def] at *
  intro x hx
  simp
  simp at h
  specialize h x
  apply h
  exact hx
  intro h
  rw [Set.subset_def] at *
  intro y hy
  simp at h
  simp at hy
  obtain ⟨x, hx, hfx⟩ := hy
  rw [← hfx]
  apply h
  exact hx

-- Proof 2 (automatic)
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  exact image_subset_iff

-- Proof 3 (equilibrated)
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  intro h
  rw [Set.subset_def] at *
  intro x hx
  simp; simp at h
  exact h x hx
  intro h
  rw [Set.subset_def] at *
  simp at *
  intro y hy
  exact h y hy


-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    id ⁻¹' S = S
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : id ⁻¹' S = S := by
  ext x
  rw [preimage]
  constructor
  intro h
  exact h
  intro h
  exact h

-- Proof 2 (automatic)
example : id ⁻¹' S = S := by
  exact rfl

-- Proof 3 (equilibrated)
example : id ⁻¹' S = S := by
  ext x
  simp


-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    id '' S = S
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : id '' S = S := by
  ext x
  rw [image]
  constructor
  intro h
  simp at h
  exact h
  intro h
  simp
  exact h

-- Proof 2 (automatic)
example : id '' S = S := by
  exact image_id S

-- Proof 3 (equilibrated)
example : id '' S = S := by
  ext x
  simp


-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U)
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  constructor
  intro h
  rw [preimage, preimage] at *
  simp at *
  exact h

-- Proof 2 (automatic)
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  exact rfl

-- Proof 3 (equilibrated)
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  simp


-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    g ∘ f '' S = g '' (f '' S)
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : g ∘ f '' S = g '' (f '' S) := by
  ext x
  rw [image, image, image]
  constructor
  intro h
  simp at *
  exact h
  intro h
  simp at *
  exact h

-- Proof 2 (automatic)
example : g ∘ f '' S = g '' (f '' S) := by
  exact image_comp g f S

-- Proof 3 (equilibrated)
example : g ∘ f '' S = g '' (f '' S) := by
  ext x
  simp


-- ---------------------------------------------------------------------
-- Exercise 8. Prove that
--    ∀ x, f x = 37 → False
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example (f : ℕ → ℕ) (h : ∀ x, f x = 37) : False := by
  sorry

-- Proof 2 (automatic)
example (f : ℕ → ℕ) (h : ∀ x, f x = 37) : False := by
  sorry

-- Proof 3 (equilibrated)
example (f : ℕ → ℕ) (h : ∀ x, f x = 37) : False := by
  sorry
