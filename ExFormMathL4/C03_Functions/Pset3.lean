-- C03_Functions/Pset3.lean
-- Problem set 3
-- Gabriel Sierra Gallego.
-- Seville, November 03, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we work with some inductive types and prove results about them by cases.
--
-- It is based on [Section03functions/Sheet3.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic
import ExFormMathL4.C03_Functions.Pset1

namespace Section3sheet3

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
  rfl


open Function
open Section3sheet1

theorem gf_injective : Injective (g ∘ f) := by
  simp [injective_def, comp_eval]

example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Injective (ψ ∘ φ) → Injective ψ := by
  change (∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Injective (ψ ∘ φ) → Injective ψ) → False
  intro h
  sorry

theorem gf_surjective : Surjective (g ∘ f) := by
  rw [surjective_def]
  intro z
  use X.a


example : ¬∀ A B C : Type, ∀ (φ : A → B) (ψ : B → C), Surjective (ψ ∘ φ) → Surjective φ := by
  sorry

end Section3sheet3
