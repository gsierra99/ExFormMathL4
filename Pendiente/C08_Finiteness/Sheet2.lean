import Mathlib.Tactic


variable (X : Type)
open scoped Classical
noncomputable section


example : Lattice (Finset X) :=
  inferInstance

--------------------------------------------------------------------------------

example (a b : Finset X) : Finset X :=
  a ⊔ b

--------------------------------------------------------------------------------

example : Finset X :=
  ⊥

--------------------------------------------------------------------------------

variable (Y : Type) (f : X → Y)

example (S : Finset X) : Finset Y :=
  Finset.image f S

--------------------------------------------------------------------------------

example (S : Finset X) : Finset Y :=
  S.image f

--------------------------------------------------------------------------------

example (S : Finset X) (y : Y) : y ∈ S.image f ↔ ∃ x ∈ S, f x = y := by
  constructor
  intro h
  exact Finset.mem_image.mp h
  intro h
  exact Finset.mem_image.mpr h

--------------------------------------------------------------------------------

example (S : Finset X) (x : X) (hx : x ∈ S) : f x ∈ S.image f := by
  exact Finset.mem_image_of_mem f hx

--------------------------------------------------------------------------------

example (S T : Finset X) (h : S ≤ T) : S.image f ≤ T.image f := by
  intro y
  intro hy
  refine Finset.mem_image.mpr ?_
  rw [Finset.mem_image] at hy
  obtain ⟨x, hxS⟩ := hy
  use x
  constructor
  have h : x ∈ S → x ∈ T := by exact fun a => h a
  apply h
  exact hxS.1
  exact hxS.2
