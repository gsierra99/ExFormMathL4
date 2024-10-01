import Mathlib.Tactic

variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  trivial

example : False → ¬True := by
  intro (hF : False)
  change True → False
  intro (_hT : True)
  exact hF

example : ¬False → True := by
  intro (hnF : ¬ False)
  change False → False at hnF
  trivial

example : True → ¬False := by
  intro (_hT : True)
  change False → False
  intro (hF : False)
  exact hF

example : False → ¬P := by
  intro (hF : False)
  change P → False
  intro (_hP : P)
  exact hF

example : P → ¬P → False := by
  intro (hP : P) (hnP : ¬P)
  change P → False at hnP
  apply hnP at hP
  exact hP

example : P → ¬¬P := by
  change P → ¬ (P → False)
  change P → ((P → False) → False)
  intro (hP : P) (hnP : P → False)
  apply hnP at hP
  exact hP

example : (P → Q) → ¬Q → ¬P := by
  change (P → Q) → (Q → False) → (P → False)
  intro (hPQ : P → Q) (hnQ : Q → False) (hP : P)
  apply hPQ at hP
  apply hnQ at hP
  exact hP

example : ¬¬False → False := by
  intro h
  apply h
  intro h2
  exact h2

example : ¬¬P → P := by
  change ((P → False) → False) → P
  intro (hnnP : (P → False) → False)
  by_contra hnP
  apply hnnP at hnP
  exact hnP

example : (¬Q → ¬P) → P → Q := by
  intro (nQnP : ¬Q → ¬P) (hP : P)
  by_contra hnQ
  apply nQnP at hnQ
  apply hnQ at hP
  exact hP
