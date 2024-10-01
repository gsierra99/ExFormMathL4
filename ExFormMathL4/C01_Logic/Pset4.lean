import Mathlib.Tactic

variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro (hPyQ : P ∧ Q)
  cases' hPyQ with hP hQ
  exact hP

example : P ∧ Q → Q := by
  intro (hPyQ : P ∧ Q)
  cases' hPyQ with hP hQ
  exact hQ

example : (P → Q → R) → P ∧ Q → R := by
  intro (hPQR : P → Q → R) (hPyQ : P ∧ Q)
  cases' hPyQ with hP hQ
  apply hPQR at hP
  apply hP at hQ
  exact hQ

example : P → Q → P ∧ Q := by
  intro (hP : P) (hQ : Q)
  constructor
  exact hP
  exact hQ

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro (hPyQ : P ∧ Q)
  cases' hPyQ with hP hQ
  constructor
  exact hQ
  exact hP

example : P → P ∧ True := by
  intro (hP : P)
  constructor
  exact hP
  trivial

example : False → P ∧ False := by
  intro (hF : False)
  constructor
  exfalso
  exact hF
  exact hF

example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro (hPyQ : P ∧ Q) (hQyR : Q ∧ R)
  cases' hPyQ with hP hQ
  cases' hQyR with hQ hR
  constructor
  exact hP
  exact hR

example : (P ∧ Q → R) → P → Q → R := by
  intro (hPyQR : P ∧ Q → R) (hP : P) (hQ : Q)
  have hPyQ : P ∧ Q := ⟨hP, hQ⟩
  apply hPyQR at hPyQ
  exact hPyQ
