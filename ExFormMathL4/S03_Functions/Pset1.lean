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

example : Injective (id : X → X) := by
  rw [injective_def]
  intro a b hid
  rw [id_eval] at hid
  exact hid

example : Surjective (id : X → X) := by
  rw [surjective_def]
  intro b
  use b
  exact rfl

example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  rw [injective_def] at *
  intro a b h
  apply hg at h
  apply hf at h
  exact h

example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  rw [surjective_def]
  intro z
  have h : ∃ y, g y = z := hg z
  cases' h with y hy
  obtain ⟨x, hx⟩ := hf y
  use x
  calc
    g (f x) = g y := by rw [hx]
    _ = z := by rw [hy]

example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  sorry

example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  sorry

end Section3sheet1
