-- C03_Functions/Pset1.lean
-- Problem set 1: inyectivity, surjectivity, biyectivity.
-- Gabriel Sierra Gallego.
-- Seville, November 03, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with inyectivity,
--surjectivity, biyectivity of functions.
--
-- It is based on [Section03functions/Sheet1.lean](https://tinyurl.com/2bbg8hdw)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

namespace Section3sheet1

open Function

variable (X Y Z : Type)
variable (x : X)
variable (f : X → Y)
variable (g : Y → Z)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that f is injective iff
--    ∀ a b : X, f a = f b → a = b
-- ---------------------------------------------------------------------

theorem injective_def :
  Injective f ↔ ∀ a b : X, f a = f b → a = b :=
by rfl

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that f is surjective iff
--    ∀ b : Y, ∃ a : X, f a = b
-- ---------------------------------------------------------------------

theorem surjective_def :
  Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b :=
by rfl

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    id x = x
-- ---------------------------------------------------------------------

theorem id_eval : id x = x :=
by rfl

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    (g ∘ f) x = g (f x)
-- ---------------------------------------------------------------------

theorem comp_eval : (g ∘ f) x = g (f x) :=
by rfl

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that the identity function is injective.
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example : Injective (id : X → X) :=
by
  rw [injective_def]
  -- ⊢ ∀ (a b : X), id a = id b → a = b
  intro a b hid
  -- a b : X
  -- hid : id a = id b
  -- ⊢ a = b
  rw [id_eval, id_eval] at hid
  -- hid : a = b
  exact hid

-- Proof 2
-- =======

example : Injective (id : X → X) :=
by
  simp [injective_def, id_eval]

-- Proof 3
-- =======

example : Injective (id : X → X) :=
  fun a b h => by
    rw [id_eval, id_eval] at h
    exact h

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example : Injective (id : X → X) :=
by
  intro a b h
  -- a b : X
  -- h : id a = id b
  -- ⊢ a = b
  exact h

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
-- =======

example : Injective (id : X → X) :=
fun _ _ h => h

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
-- =======

example : Injective (id : X → X) :=
injective_id

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
