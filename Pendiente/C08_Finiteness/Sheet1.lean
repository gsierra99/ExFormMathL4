import Mathlib.Tactic

--------------------------------------------------------------------------------
example (X : Type) (S : Set X) (hS : Set.Finite S) : S = S := by
  rfl

--------------------------------------------------------------------------------
example (X : Type) (S : Set X) (hS : S.Finite) : S = S := by
  rfl

--------------------------------------------------------------------------------
example (X : Type) (S : Set X) (T : Set X) (hs : Set.Finite S) (ht : T.Finite) : (S ∪ T).Finite :=
  by
  exact Set.Finite.union hs ht

--------------------------------------------------------------------------------

variable (X : Type)


example (S : Finset X) : (S : Set X) = (S : Set X) := by
  rfl

--------------------------------------------------------------------------------
example (S : Finset X) : Set.Finite (S : Set X) :=
  by exact Finset.finite_toSet S

--------------------------------------------------------------------------------

open BigOperators

example (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℚ) ^ 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by

  induction' n with d hd
  ·
    simp
  ·
    rw [Finset.sum_range_succ]
    rw [hd]
    simp
    ring

--------------------------------------------------------------------------------
example (n : ℕ) : ∑ i in Finset.range n, (i : ℚ) ^ 3 = (n : ℚ) ^ 2 * (n - 1) ^ 2 / 4 := by
  induction' n with d hd
  ·
    simp
  ·
    rw [Finset.sum_range_succ]
    rw [hd]
    simp
    ring
