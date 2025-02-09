
import Mathlib.Tactic

section PropVersion


variable (X : Type) [Finite X]


variable (Y : Type) [Finite Y]

example : Finite (X × Y) :=
  inferInstance

--------------------------------------------------------------------------------

example : Finite (X → Y) :=
  inferInstance

--------------------------------------------------------------------------------

example : Fin 37 :=
  ⟨3, by linarith⟩

--------------------------------------------------------------------------------

example : Finite (Fin 37) :=
  inferInstance

--------------------------------------------------------------------------------

end PropVersion


variable (X : Type) [Fintype X]

example : X = X := by
  rename_i foo
  cases foo
  rfl

--------------------------------------------------------------------------------

example (n : ℕ) : Fintype (Fin n) :=
  inferInstance

open scoped BigOperators


example : ∑ x : Fin 10, x = 45 := by
  rfl

--------------------------------------------------------------------------------

example : ∑ x : Fin 10, x = 25 := by
  rfl

--------------------------------------------------------------------------------

example : ∑ x : Fin 10, x.val = 45 := by
  rfl
