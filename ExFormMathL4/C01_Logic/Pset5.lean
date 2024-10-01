import Mathlib.Tactic

variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro (hPiffQ : P ↔ Q)
  rw [hPiffQ]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro (hPiffQ : P ↔ Q)
  rw [hPiffQ]
  intro (hQiffP : Q ↔ P)
  rw [hQiffP]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro (hPiffQ : P ↔ Q)
  intro (hQiffR : Q ↔ R)
  rw [hPiffQ, hQiffR]

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro (hPyQ : P ∧ Q)
  cases' hPyQ with hP hQ
  constructor
  exact hQ
  exact hP
  intro (hQyP : Q ∧ P)
  cases' hQyP with hQ hP
  constructor
  exact hP
  exact hQ

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro hPyQyR
  cases' hPyQyR with hPyQ hR
  cases' hPyQ with hP hQ
  constructor
  exact hP
  constructor
  exact hQ
  exact hR
  intro hPyQyR
  cases' hPyQyR with hP hQyR
  cases' hQyR with hQ hR
  constructor
  constructor
  exact hP
  exact hQ
  exact hR

example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  exact hP
  trivial
  intro hPyT
  cases' hPyT with hP hT
  exact hP

example : False ↔ P ∧ False := by
  constructor
  intro hF
  constructor
  exfalso
  exact hF
  exact hF
  intro hPyF
  cases' hPyF with hP hF
  exact hF

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPiffQ hRiffS
  rw [hPiffQ, hRiffS]

example : ¬(P ↔ ¬P) := by
  -- change (P ↔ ¬P) → False
  -- intro hPiffnP
  -- cases' hPiffnP with hPnP hnPP
  -- apply hPnP
  -- by_contra hnP
  tauto

example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := by
    cases' h with h1 h2
    intro hP
    apply h1 <;> assumption
  apply hnP
  rw [h]
  exact hnP
