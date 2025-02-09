
import Mathlib.Tactic

namespace Section9sheet3


example (X : Type) : X ≃ X :=
  { toFun := fun x ↦ x
    invFun := fun y ↦ y
    left_inv := by
      exact congrFun rfl
    right_inv := by
      exact congrFun rfl }

--------------------------------------------------------------------------------

example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.invFun
    invFun := e.toFun
    left_inv := by
      unfold Function.LeftInverse
      intro x
      simp
    right_inv := by
      unfold Function.RightInverse
      intro y
      simp }

--------------------------------------------------------------------------------

example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.symm
    invFun := e
    left_inv := e.right_inv
    right_inv := e.left_inv }

--------------------------------------------------------------------------------

example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  { toFun := fun x => eYZ (eXY x)
    invFun := fun z => eXY.symm (eYZ.symm z)
    left_inv := by
      unfold Function.LeftInverse
      intro x
      simp
    right_inv := by
      unfold Function.RightInverse
      intro z
      simp }

--------------------------------------------------------------------------------

example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  Equiv.trans eXY eYZ

--------------------------------------------------------------------------------

example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  eXY.trans eYZ

--------------------------------------------------------------------------------

example (A B X : Type) (eAX : A ≃ X) (eBX : B ≃ X) : A ≃ B := eAX.trans (eBX.symm)


--------------------------------------------------------------------------------

def R (X Y : Type) : Prop :=
  ∃ e : X ≃ Y, True


example : Equivalence R := by
  sorry
