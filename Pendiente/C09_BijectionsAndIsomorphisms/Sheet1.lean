
import Mathlib.Tactic

variable (X Y : Type) (f : X → Y)


example : Prop :=
  Function.Bijective f


example : Prop :=
  f.Bijective


example : f.Bijective ↔ f.Injective ∧ f.Surjective := by
  rfl

example : f.Bijective ↔
    (∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂) ∧ ∀ y : Y, ∃ x : X, f x = y := by
  rfl


example : (∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id) → f.Bijective := by
  intro hg
  obtain ⟨g, hg1, hg2⟩ := hg
  have defbiy : f.Bijective = (f.Injective ∧ f.Surjective) := by rfl
  rw [defbiy]
  constructor
  rw [Function.Injective]
  intro x₁ x₂ h
  have hgof : ∀ x : X, g (f x) = x :=
    fun x => congrFun hg2 x
  rw [←hgof x₁, ←hgof x₂]
  rw [h]
  rw [Function.Surjective]
  intro y
  use g y
  have hfog : ∀ y : Y, f (g y) = y :=
    fun y => congrFun hg1 y
  rw [hfog y]


example : f.Bijective → ∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id := by
  intro h
  unfold Function.Bijective at h
  obtain ⟨hi, hs⟩ := h
  choose g hg using hs
  use g
  constructor
  rw [Function.LeftInverse.comp_eq_id hg]
  unfold Function.Injective at hi
  funext x
  simp
  exact hi (hg (f x))
