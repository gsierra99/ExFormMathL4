-- C03_Functions/Pset1.lean
-- Problem set 1: inyectivity, surjectivity, biyectivity.
-- Gabriel Sierra Gallego.
-- Seville, November 03, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with inyectivity, surjectivity, biyectivity of functions.
--
-- It is based on [Section03functions/Sheet1.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic -- imports all the Lean tactics

namespace Section3sheet1

open Function

variable (X Y Z : Type)

theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl

theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b := by
  rfl

theorem id_eval (x : X) : id x = x := by
  rfl

theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl


-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    Injective (id : X → X)
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : Injective (id : X → X) := by
  rw [injective_def]
  intro a b hid
  rw [id_eval, id_eval] at hid
  exact hid

-- Proof 2 (automatic)
example : Injective (id : X → X) := by
  simp [injective_def, id_eval]

-- Proof 3 (equilibrated)
example : Injective (id : X → X) :=
  fun a b h => by
    rw [id_eval, id_eval] at h
    exact h


-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    Surjective (id : X → X)
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : Surjective (id : X → X) := by
  rw [surjective_def]
  intro b
  use b
  exact rfl

-- Proof 2 (automatic)
example : Surjective (id : X → X) := by
  simp [surjective_def, id_eval]

-- Proof 3 (equilibrated)
example : Surjective (id : X → X) :=
  fun b => by
    use b
    exact rfl

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f)
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  rw [injective_def] at *
  intro a b h
  rw [comp_eval, comp_eval] at h
  apply hg at h
  apply hf at h
  exact h

-- Proof 2 (automatic)
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  exact Injective.comp hg hf

-- Proof 3 (equilibrated)
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  simp [injective_def, comp_eval]
  intro a b h
  apply hg at h
  apply hf at h
  exact h

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f)
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  rw [surjective_def] at *
  intro z
  have h : ∃ y, g y = z := hg z
  cases' h with y hy
  obtain ⟨x, hx⟩ := hf y
  use x
  calc
    g (f x) = g y := by rw [hx]
    _ = z := by rw [hy]

-- Proof 2 (automatic)
example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  exact Surjective.comp hg hf

-- Proof 3 (equilibrated)
example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  rw [surjective_def] at *
  simp [comp_eval]
  intro z
  specialize hg z
  obtain ⟨y, hy⟩ := hg
  specialize hf y
  obtain ⟨x, hx⟩ := hf
  use x
  simp [hx, hy]

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    Injective (g ∘ f) → Injective f
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  rw [injective_def]
  intro h a b hab
  apply h
  rw [comp_eval, comp_eval, hab]

-- Proof 2 (automatic)
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  exact fun a => Injective.of_comp a

-- Proof 3 (equilibrated)
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  simp [injective_def, comp_eval]
  intro h a b hab
  apply h
  simp [hab]

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    Surjective (g ∘ f) → Surjective g
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  rw [surjective_def]
  intro h
  rw [surjective_def]
  intro z
  specialize h z
  obtain ⟨x, hx⟩ := h
  rw [comp_eval] at hx
  use (f x)

-- Proof 2 (automatic)
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  exact fun a => Surjective.of_comp a


-- Proof 3 (equilibrated)
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  simp [surjective_def, comp_eval]
  intro h z
  specialize h z
  obtain ⟨x, hx⟩ := h
  use (f x)


end Section3sheet1
