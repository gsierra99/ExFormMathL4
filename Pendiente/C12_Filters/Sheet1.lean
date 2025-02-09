import Mathlib.Tactic

import Mathlib.Order.Filter.Basic


namespace Section12sheet1

open Filter Set

variable (α : Type) (F : Filter α) (S T : Set α)


example : S ∩ T ∈ F ↔ S ∈ F ∧ T ∈ F := by
  constructor
  intro h
  constructor
  have h' : S ∩ T ⊆ S := inter_subset_left
  exact mem_of_superset h h'
  have h' : S ∩ T ⊆ T := inter_subset_right
  exact mem_of_superset h h'
  intro h
  exact inter_mem_iff.mpr h


example (X : Set α) : Filter α where
  sets := { S | X ⊆ S }
  univ_sets := by
    exact subset_univ X
  sets_of_superset := by
    intros A B hAB hAsB
    simp at *
    exact (Subset.trans hAB hAsB)
  inter_sets := by
    intros A B hAs hBs
    simp at *
    constructor
    assumption
    assumption


open scoped Filter


namespace Section12sheet1
