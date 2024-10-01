import Mathlib.Tactic

open Set

variable (X : Type)
variable (A B C D E : Set X)
variable (x y z : X)

open Set

example : x ∈ (univ : Set X) := by
  trivial

example : x ∈ (∅ : Set X) → False := by
  intro h
  cases h

example : A ⊆ univ := by
  rw [subset_def]
  intro x _hxA
  trivial

example : ∅ ⊆ A := by
  rw [subset_def]
  intro x hx
  cases hx
