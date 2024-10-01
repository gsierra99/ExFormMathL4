import Mathlib.Tactic

open Set

variable (X : Type)
variable (A B C D E : Set X)
variable (x y z : X)

example : x ∉ A → x ∈ A → False := by
  intro hxnA hxA
  apply hxnA
  exact hxA

example : x ∈ A → x ∉ A → False := by
  intro hxA hxnA
  apply hxnA
  exact hxA

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAinB hxninB
  rw [subset_def] at hAinB
  by_contra hxinA
  apply hAinB at hxinA
  apply hxninB
  exact hxinA

example : x ∉ (∅ : Set X) := by
  by_contra hxinv
  cases hxinv

example : x ∈ Aᶜ → x ∉ A := by
  intro hxinAc
  by_contra hxninAc
  exact hxinAc hxninAc

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  intro hAisU
  by_contra hExinAc
  cases' hExinAc with x hxinAyC
  apply hAisU at x
  apply hxinAyC at x
  cases x
  intro hnExinAc
  intro x
  by_contra hxninA
  sorry

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  sorry
