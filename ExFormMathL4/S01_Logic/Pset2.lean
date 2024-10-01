import Mathlib.Tactic

variable (P Q R : Prop)

example : True := by
  trivial

example : True → True := by
  trivial

example : False → True := by
  intro False
  exfalso
  exact False

example : False → False := by
  intro False
  exact False

example : (True → False) → False := by
  intro (hTF : True → False)
  apply hTF
  trivial

example : False → P := by
  intro False
  exfalso
  exact False

example : True → False → True → False → True → False := by
  intro _h1 h2 _h3 _h4 _h5
  exact h2

example : P → (P → False) → False := by
  intro (hP : P) (hPF : P → False)
  apply hPF at hP
  exact hP

example : (P → False) → P → Q := by
  intro (hPF : P → False) (hP : P)
  exfalso
  apply hPF at hP
  exact hP

example : (True → False) → P := by
  intro (hTF : True → False)
  exfalso
  apply hTF
  trivial
