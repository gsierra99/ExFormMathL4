import Mathlib.Tactic

namespace Section4sheet4

theorem mem_def (X : Type) (P : X → Prop) (a : X) :
    a ∈ {x : X | P x} ↔ P a := by
  rfl

open Set

def IsEven (n : ℕ) : Prop :=
  ∃ t, n = 2 * t

theorem IsEven_def {n : ℕ} : IsEven n ↔ ∃ t, n = 2 * t := by
  rfl

example : 74 ∈ {n : ℕ | IsEven n} := by
  rw [mem_def]
  rw [IsEven_def]
  use 37

def Real.IsEven (r : ℝ) :=
  ∃ t : ℝ, r = 2 * t

theorem Real.IsEven_def {r : ℝ} : Real.IsEven r ↔ ∃ t : ℝ, r = 2 * t := by
  rfl

example : ∀ x, x ∈ {r : ℝ | Real.IsEven r} := by
  intro x
  rw [mem_def]
  rw [Real.IsEven_def]
  use x/2
  ring

example : ∀ x, x ∉ {r : ℝ | 0 < r ∧ r < 0} := by
  intro x
  simp
  intro h
  exact le_of_lt h
