import Mathlib.Tactic

variable (P Q R : Prop)

-- Example 1: ¬True → False

-- Detailed proof
example : ¬True → False := by
  intro hnT
  change True → False at hnT
  apply hnT
  exact True.intro

-- Automatic proof
example : ¬True → False := by
  intro hnT
  contradiction

-- Balanced proof
example : ¬True → False := by
  intro hnT
  have hT : True := True.intro
  contradiction


-- Example 2: False → ¬True

-- Detailed proof
example : False → ¬True := by
  intro hF
  change True → False
  intro hT
  exact hF

-- Automatic proof
example : False → ¬True := by
  trivial

-- Balanced proof
example : False → ¬True := by
  intro hF
  tauto


-- Example 3: ¬False → True

-- Detailed proof
example : ¬False → True := by
  intro hnF
  exact True.intro

-- Automatic proof
example : ¬False → True := by
  tauto

-- Balanced proof
example : ¬False → True := by
  intro hnF
  trivial


-- Example 4: True → ¬False

-- Detailed proof
example : True → ¬False := by
  intro hT
  change False → False
  intro hF
  exact hF

-- Automatic proof
example : True → ¬False := by
  tauto

-- Balanced proof
example : True → ¬False := by
  intro hT
  change False → False
  trivial


-- Example 5: False → ¬P

-- Detailed proof
example : False → ¬P := by
  intro hF
  change P → False
  intro hP
  exact hF

-- Automatic proof
example : False → ¬P := by
  tauto

-- Balanced proof
example : False → ¬P := by
  intro hF
  contradiction


-- Example 6: P → ¬P → False

-- Detailed proof
example : P → ¬P → False := by
  intro hP hnP
  change P → False at hnP
  apply hnP
  exact hP

-- Automatic proof
example : P → ¬P → False := by
  tauto

-- Balanced proof
example : P → ¬P → False := by
  intro hP hnP
  contradiction


-- Example 7: P → ¬¬P

-- Detailed proof
example : P → ¬¬P := by
  intro hP
  change (P → False) → False
  intro hnP
  have hF : False := hnP hP
  exact hF

-- Automatic proof
example : P → ¬¬P := by
  tauto

-- Balanced proof
example : P → ¬¬P := by
  intro hP
  change (P → False) → False
  intro hnP
  contradiction


-- Example 8: (P → Q) → ¬Q → ¬P

-- Detailed proof
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  change P → False
  intro hP
  apply hPQ at hP
  apply hnQ at hP
  exact hP

-- Automatic proof
example : (P → Q) → ¬Q → ¬P := by
  tauto

-- Balanced proof
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  apply hPQ at hP
  contradiction


-- Example 9: ¬¬False → False

-- Detailed proof
example : ¬¬False → False := by
  intro hnnF
  change (False → False) → False at hnnF
  apply hnnF
  intro hF
  exact hF

-- Automatic proof
example : ¬¬False → False := by
  tauto

-- Balanced proof
example : ¬¬False → False := by
  intro hnnF
  have hF : False := by tauto
  exact hF


-- Example 10: ¬¬P → P

-- Detailed proof
example : ¬¬P → P := by
  intro hnnP
  change (P → False) → False at hnnP
  by_contra hnP
  apply hnnP
  exact hnP

-- Automatic proof
example : ¬¬P → P := by
  tauto

-- Balanced proof
example : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  apply hnnP at hnP
  exact hnP


-- Example 11: (¬Q → ¬P) → P → Q

-- Detailed proof
example : (¬Q → ¬P) → P → Q := by
  intro nQnP hP
  by_contra hnQ
  apply nQnP at hnQ
  apply hnQ at hP
  exact hP

-- Automatic proof
example : (¬Q → ¬P) → P → Q := by
  tauto

-- Balanced proof
example : (¬Q → ¬P) → P → Q := by
  intro nQnP hP
  by_contra hnQ
  apply nQnP at hnQ
  contradiction
