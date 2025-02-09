
import Mathlib.Tactic

namespace Section10sheet1

noncomputable section


open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false


example : TopologicalSpace X where
  IsOpen (s : Set X) := True
  isOpen_univ := by
    trivial
  isOpen_inter := by
    intros s t
    intros hs ht
    trivial
  isOpen_sUnion := by
    intro F
    intro hF
    trivial

--------------------------------------------------------------------------------

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ
  isOpen_univ := by
    right
    dsimp
  isOpen_inter := by
    rintro s t (rfl | rfl) (rfl | rfl)
    -- four cases
    · left
      simp
    · left
      simp
    · left
      simp
    · right
      simp
  isOpen_sUnion := by
    intro F hF
    by_cases h : Set.univ ∈ F
    · right
      aesop
    · left
      have foo : ∀ s ∈ F, s = ∅ := by -- key intermediate step
        by_contra! h2
        rcases h2 with ⟨s, hs1, hs2⟩
        specialize hF s hs1
        aesop
      exact Set.sUnion_eq_empty.mpr foo -- found with `exact?`

--------------------------------------------------------------------------------

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  simp

--------------------------------------------------------------------------------

#synth TopologicalSpace ℝ


def Real.IsOpen (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  unfold Real.IsOpen
  intro x hx
  use 1
  constructor
  simp
  intro y hy
  assumption

--------------------------------------------------------------------------------

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  obtain ⟨δs, δspos, hs⟩ := hs x (by aesop)
  obtain ⟨δt, δtpos, ht⟩ := ht x (by aesop)
  use min δs δt, by positivity
  rintro y ⟨h1, h2⟩
  constructor
  · apply hs
    have foo : min δs δt ≤ δs := min_le_left δs δt
    constructor <;> linarith
  · apply ht
    have foo : min δs δt ≤ δt := min_le_right δs δt
    constructor <;> linarith

--------------------------------------------------------------------------------

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  simp_rw [Set.mem_sUnion] at hx ⊢
  rcases hx with ⟨t, htF, hxt⟩
  obtain ⟨δ, hδpos, h⟩ := hF t htF x hxt
  use δ, hδpos
  peel h with h1 y hyt
  use t, htF


example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
