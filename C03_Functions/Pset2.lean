import Mathlib.Tactic

namespace Section3sheet2

inductive X : Type
  | a : X
  | b : X
  | c : X

open X

-- #check a
-- su valor es X

example (x : X) : x = a ∨ x = b ∨ x = c := by
  cases x with
  | a => left; rfl
  | b => right; left; rfl
  | c => right; right; rfl

example : a ≠ b := by
  intro h
  cases h

def f : X → ℕ
  | a => 37
  | b => 42
  | c => 0

example : f a = 37 := by
  rfl

example : Function.Injective f := by
  intro x y h
  cases x <;> cases y
  all_goals try rfl
  all_goals cases h

end Section3sheet2
