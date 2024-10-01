import Mathlib.Tactic

namespace Section3sheet1

inductive X : Type
  | a : X

inductive Y : Type
  | b : Y
  | c : Y

inductive Z : Type
  | d : Z

def f : X → Y
  | X.a => Y.b

def g : Y → Z
  | Y.b => Z.d
  | Y.c => Z.d

example (z : Z) : z = Z.d := by
  cases z
  rfl

theorem Yb_ne_Yc : Y.b ≠ Y.c := by
  intro h
  cases h

theorem gYb_eq_gYc : g Y.b = g Y.c := by
  sorry

open Function

theorem gf_injective : Injective (g ∘ f) := by
  sorry

example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Injective (ψ ∘ φ) → Injective ψ := by
  sorry

theorem gf_surjective : Surjective (g ∘ f) := by
  sorry

example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ := by
  sorry

end Section3sheet1
