-- C01_Logic/Pset3.lean
-- Problem set 3: The negation.
-- Gabriel Sierra Gallego.
-- Seville, October 22, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with the `not` in Lean4.
--
-- It is based on [Section01logic/Sheet3.lean](https://tinyurl.com/279t67ga)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

variable (P Q R : Prop)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    ¬True → False
-- ---------------------------------------------------------------------

-- Proof 1
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  change True → False at hnT
  -- hnT : True → False
  apply hnT
  -- ⊢ True
  exact True.intro

-- Proof 2
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  contradiction

-- Proof 3
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  have hT : True := True.intro
  contradiction

-- Comentario de JA: En la demostración anterior se puede evitar el uso
-- de la táctica contradiction como se muestra a continuación.

-- Proof 4
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  have hT : True := True.intro
  exact hnT hT

-- Comentario de JA: La demostración anterior se puede simplificar como
-- se muestra a continuación.

-- Proof 5
example : ¬True → False := by
  intro hnT
  -- hnT : ¬True
  -- ⊢ False
  exact hnT True.intro

-- Comentario de JA: La demostración anterior se puede refactorizar como
-- se muestra a continuación.

-- Proof 6
example : ¬True → False :=
  fun hnT => hnT True.intro

-- Comentario de JA: Se puede demostrar automáticamente como se muestra
-- a continuación.

-- Proof 7
example : ¬True → False := by
  decide

-- Proof 8
example : ¬True → False := by
  tauto

-- Example 2: False → ¬True

-- Detailed proof
example : False → ¬True := by
  intro hF
  change True → False
  intro _hT
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
  intro _hnF
  exact True.intro

-- Automatic proof
example : ¬False → True := by
  tauto

-- Balanced proof
example : ¬False → True := by
  intro _hnF
  trivial


-- Example 4: True → ¬False

-- Detailed proof
example : True → ¬False := by
  intro _hT
  change False → False
  intro hF
  exact hF

-- Automatic proof
example : True → ¬False := by
  tauto

-- Balanced proof
example : True → ¬False := by
  intro _hT
  change False → False
  trivial


-- Example 5: False → ¬P

-- Detailed proof
example : False → ¬P := by
  intro hF
  change P → False
  intro _hP
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
