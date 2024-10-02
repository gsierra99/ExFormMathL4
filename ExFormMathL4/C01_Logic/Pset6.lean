import Mathlib.Tactic -- imports all the Lean tactics

variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  cases' hPoQ with hP hQ
  apply hPR at hP
  exact hP
  apply hQR at hQ
  exact hQ

example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  right
  exact hP
  left
  exact hQ

example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  -- constructor
  -- intro hPoQoR
  -- cases' hPoQoR with hPoQ hR
  -- cases' hPoQ with hP hQ
  -- left
  -- exact hP
  -- right
  -- left
  -- exact hQ
  -- right
  -- right
  -- exact hR
  tauto

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  cases' hPoQ with hP hQ
  apply hPR at hP
  left
  exact hP
  apply hQS at hQ
  right
  exact hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  cases' hPoR with hP hR
  apply hPQ at hP
  left
  exact hP
  right
  exact hR

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPiffR hQiffR
  rw [hPiffR, hQiffR]

example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  -- change ((P ∨ Q) → False) ↔ ((P → False) ∧ (Q → False))
  -- constructor
  -- intro hPoQF
  -- constructor
  -- intro hP
  tauto

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  tauto
