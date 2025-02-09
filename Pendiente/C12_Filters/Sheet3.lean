
import Mathlib.Tactic

import Mathlib.Order.Filter.Basic


namespace Section12sheet3

open Set

def atTop (L : Type) [LinearOrder L] (e : L) : Filter L where
  sets := {X : Set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
  univ_sets := by
    simp
    use e
  sets_of_superset := by
    intros S T hST hS
    simp at *
    obtain ⟨x, hx⟩ := hST
    use x
    intro y hy
    exact hS (hx y hy)
  inter_sets := by
    intros S T hS hT
    simp at *
    obtain ⟨x, hx⟩ := hS
    obtain ⟨z, hz⟩ := hT
    use max x z
    intro y hy
    specialize hx y
    specialize hz y
    have h : x ≤ y := by exact le_of_max_le_left hy
    have h' : z ≤ y := by exact le_of_max_le_right hy
    exact ⟨hx h, hz h'⟩


def cofinite (α : Type) : Filter α where
  sets := {S : Set α | Sᶜ.Finite}
  univ_sets := by
    simp
  sets_of_superset := by
    intros S T hST hS
    simp at *
    rw [←compl_subset_compl] at hS
    exact Finite.subset hST hS
  inter_sets := by
    intros S T hS hT
    simp at *
    rw [compl_inter]
    exact Finite.union hS hT

/-

## Harder exercises.

If you like this filter stuff, then formalise in Lean and prove the following:

(1) prove that the cofinite filter on a finite type is the entire power set filter (`⊥`).
(2) prove that the cofinite filter on `ℕ` is equal to the `atTop` filter.
(3) Prove that the cofinite filter on `ℤ` is not equal to the `atTop` filter.
(4) Prove that the cofinite filter on `ℕ` is not principal.

-/

end Section12sheet3
