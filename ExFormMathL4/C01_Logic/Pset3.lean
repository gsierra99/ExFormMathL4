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

-- Proof 9
example : ¬True → False := by
  trivial

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    False → ¬True
-- ---------------------------------------------------------------------

-- Proof 1
example : False → ¬True := by
  intro hF
  -- hF : False
  -- ⊢ ¬True
  change True → False
  -- ⊢ True → False
  intro _hT
  -- _hT : True
  -- ⊢ False
  exact hF

-- Proof 2
example : False → ¬True := by
  trivial

-- Proof 3
example : False → ¬True := by
  intro hF
  -- hF : False
  -- ⊢ ¬True
  tauto

-- Comentario de JA: La demostración anterior se puede simplificar como
-- se muestra a continuación.

-- Proof 4
example : False → ¬True := by
  tauto

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : False → ¬True := by
  intro hF
  -- hF : False
  -- ⊢ ¬True
  intro _hT
  -- _hT : True
  -- ⊢ False
  exact hF

-- Comentario de JA: La demostración anterior se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : False → ¬True :=
  fun hF _hT => hF

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : False → ¬True := by
  intro hF
  -- hF : False
  -- ⊢ ¬True
  contradiction

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    ¬False → True
-- ---------------------------------------------------------------------

-- Proof 1
example : ¬False → True := by
  intro _hnF
  -- _hnF : ¬False
  -- ⊢ True
  exact True.intro

-- Proof 2
example : ¬False → True := by
  tauto

-- Proof 3
example : ¬False → True := by
  intro _hnF
  -- _hnF : ¬False
  -- ⊢ True
  trivial

-- Comentario de JA: La demostración anterior se puede simplificar como
-- se muestra a continuación.

-- Proof 4
example : ¬False → True := by
  trivial

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : ¬False → True :=
  fun _ => True.intro

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    True → ¬False
-- ---------------------------------------------------------------------

-- Proof 1
example : True → ¬False := by
  intro _hT
  -- _hT : True
  -- ⊢ ¬False
  change False → False
  -- ⊢ False → False
  intro hF
  -- hF : False
  -- ⊢ False
  exact hF

-- Proof 2
example : True → ¬False := by
  tauto

-- Proof 3
example : True → ¬False := by
  intro _hT
  -- _hT : True
  -- ⊢ ¬False
  change False → False
  -- ⊢ False → False
  trivial

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : True → ¬False := by
  trivial

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : True → ¬False := by
  intro _hT
  -- _hT : True
  -- ⊢ ¬False
  intro hF
  -- hF : False
  -- ⊢ False
  exact hF

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : True → ¬False :=
  fun _hT hF => hF

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    False → ¬P
-- ---------------------------------------------------------------------

-- Proof 1
example : False → ¬P := by
  intro hF
  -- hF : False
  -- ⊢ ¬P
  change P → False
  -- ⊢ P → False
  intro _hP
  -- _hP : P
  -- ⊢ False
  exact hF

-- Proof 2
example : False → ¬P := by
  tauto

-- Proof 3
example : False → ¬P := by
  intro hF
  -- hF : False
  -- ⊢ ¬P
  contradiction

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : False → ¬P := by
  intro hF
  -- hF : False
  -- ⊢ ¬P
  exact False.elim hF

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : False → ¬P :=
  fun hF => False.elim hF

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    P → (¬P → False)
-- ---------------------------------------------------------------------

-- Proof 1
example : P → ¬P → False := by
  intro hP hnP
  -- hP : P
  -- hnP : ¬P
  -- ⊢ False
  change P → False at hnP
  -- hnP : P → False
  apply hnP
  -- ⊢ P
  exact hP

-- Proof 2
example : P → ¬P → False := by
  tauto

-- Proof 3
example : P → ¬P → False := by
  intro hP hnP
  contradiction

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P → ¬P → False := by
  intro hP hnP
  -- hP : P
  -- hnP : ¬P
  -- ⊢ False
  apply hnP
  -- ⊢ P
  exact hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P → ¬P → False :=
  fun hP hnP => hnP hP

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    P → ¬¬P
-- ---------------------------------------------------------------------

-- Proof 1
example : P → ¬¬P := by
  intro hP
  -- hP : P
  -- ⊢ ¬¬P
  change (P → False) → False
  -- ⊢ (P → False) → False
  intro hnP
  -- hnP : P → False
  -- ⊢ False
  have hF : False := hnP hP
  exact hF

-- Proof 2
example : P → ¬¬P := by
  tauto

-- Proof 3
example : P → ¬¬P := by
  intro hP
  -- hP : P
  -- ⊢ ¬¬P
  change (P → False) → False
  -- ⊢ (P → False) → False
  intro hnP
  -- hnP : P → False
  -- ⊢ False
  contradiction

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P → ¬¬P := by
  intro hP
  -- hP : P
  -- ⊢ ¬¬P
  intro hnP
  -- hnP : hnP : ¬P
  -- ⊢ False
  exact hnP hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P → ¬¬P :=
  fun hP hnP => hnP hP

-- ---------------------------------------------------------------------
-- Exercise 8. Prove that
--    (P → Q) → (¬Q → ¬P)
-- -----------------------------------------------------------

-- Proof 1
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  -- hPQ : P → Q
  -- hnQ : ¬Q
  -- ⊢ ¬P
  change P → False
  -- ⊢ P → False
  intro hP
  -- hP : P
  -- ⊢ False
  apply hPQ at hP
  -- hP : Q
  apply hnQ at hP
  -- hP : False
  exact hP

-- Proof 2
example : (P → Q) → ¬Q → ¬P := by
  tauto

-- Proof 3
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  -- hPQ : P → Q
  -- hnQ : ¬Q
  -- hP : P
  -- ⊢ False
  apply hPQ at hP
  -- hP : Q
  contradiction

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  -- hPQ : P → Q
  -- hnQ : ¬Q
  -- hP : P
  -- ⊢ False
  apply hnQ
  -- ⊢ Q
  apply hPQ
  -- ⊢ P
  exact hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : (P → Q) → ¬Q → ¬P :=
  fun hPQ hnQ hP => hnQ (hPQ hP)

-- Comentario de JA: La 5ª demostración se puede detallar como se
-- muestra a continuación.

-- Proof 6
example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ hP
  -- hPQ : P → Q
  -- hnQ : ¬Q
  -- hP : P
  -- ⊢ False
  have hQ : Q := hPQ hP
  show False
  exact hnQ hQ

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
