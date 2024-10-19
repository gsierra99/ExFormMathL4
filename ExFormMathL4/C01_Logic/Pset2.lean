-- C01_Logic/Pset2.lean
-- Problem set 2: True and False.
-- Gabriel Sierra Gallego.
-- Seville, October 13, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with the truth values True
-- and False in Lean4.
--
-- It is based on [Section01logic/Sheet2.lean](https://tinyurl.com/22v2rm6q)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

variable (P Q R : Prop)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    True
-- ---------------------------------------------------------------------

-- Proof 1 (Detailed)
example : True := by
  exact True.intro

-- Proof 2 (Automatic)
example : True := by
  trivial

-- Proof 3 (Balanced)
example : True := by
  constructor

-- Comentario de JA: Se puede demostrar con otras tácticas, como se
-- demuestra en las siguientes pruebas.

-- Proof 4
example : True := by
  decide

-- Proof 5
example : True := by
  tauto

-- Proof 6
example : True := by
  simp only

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    True → True
-- ---------------------------------------------------------------------

-- Proof 1 (Detailed)
example : True → True := by
  intro hT
  -- hT : True
  -- ⊢ True
  exact hT

-- Comentario de JA: La demostración anterior se puede factorizar como
-- se muestra a continuación.

-- Proof 2
example : True → True :=
  fun hT => hT

-- Proof 3 (Automatic)
example : True → True := by
  trivial

-- Comentario de JA: Se puede demostrar con otras tácticas, como se
-- muestra a continuación.

-- Proof 4
example : True → True := by
  decide

-- Proof 5
example : True → True := by
  tauto

-- Proof 6
example : True → True := by
  simp only [imp_self]

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    False → True
-- ---------------------------------------------------------------------

-- Proof 1 (Detailed)
example : False → True := by
  intro h
  -- h : False
  -- ⊢ True
  exfalso
  -- ⊢ False
  exact h

-- Comentario de JA: Se puede eliminar el uso de exfalso como se muestra
-- a continuación.

-- Proof 2
example : False → True := by
  exact False.elim

-- Comentario de JA: Se puede eliminar el uso de exact como se muestra
-- a continuación.

-- Proof 3
example : False → True :=
  False.elim

-- Proof 4 (Automatic)
example : False → True := by
  trivial

-- Comentario de JA: Se puede demostrar con otras tácticas como se
-- muestra a continuación

-- Proof 5
example : False → True := by
  decide

-- Proof 6
example : False → True := by
  tauto

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    False → False
-- ---------------------------------------------------------------------

-- Proof 1 (Detailed)
example : False → False := by
  intro h
  -- h : False
  -- ⊢ False
  exact h

-- Comentario de JA: La demostración anterior se puede refactorizar como
-- se muestra a continuación.

-- Proof 2
example : False → False :=
  fun h => h

-- Proof 3
example : False → False := by
  intro h
  -- h : False
  -- ⊢ False
  assumption

-- Proof 4 (Automatic)
example : False → False := by
  trivial

-- Comentario de JA: A continuación se muestran otras posibles
-- demostraciones.

-- Proof 5
example : False → False := by
  decide

-- Proof 6
example : False → False := by
  tauto

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    (True → False) → False
-- ---------------------------------------------------------------------

-- Proof 1 (Detailed)
example : (True → False) → False := by
  intro hTF
  -- hTF : True → False
  -- ⊢ False
  apply hTF
  -- ⊢ True
  exact True.intro

-- Comentario de JA: La demostración anterior se puede refactorizar como
-- se muestra a continuación.

-- Proof 2
example : (True → False) → False :=
  fun hTF => hTF True.intro

-- Proof 3
example : (True → False) → False := by
  intro hTF
  -- hTF : True → False
  -- ⊢ False
  contradiction

-- Proof 4
example : (True → False) → False := by
  intro hTF
  -- hTF : True → False
  -- ⊢ False
  apply hTF
  -- ⊢ True
  trivial

-- Comentario de JA: A continuación se muestran otras posibles
-- demostraciones.

-- Proof 5
example : (True → False) → False := by
  decide

-- Proof 6
example : (True → False) → False := by
  tauto

-- Proof 7
example : (True → False) → False :=
  fun a => a trivial

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    False → P
-- ---------------------------------------------------------------------

-- Proof 1 (Detailed)
example : False → P := by
  intro h
  -- h : False
  -- ⊢ P
  exfalso
  -- ⊢ False
  exact h

-- Comentario de JA: Se puede evitar usar exfalso como se muestra a
-- continuación.

-- Proof 2
example : False → P := by
  intro h
  -- h : False
  -- ⊢ P
  exact False.elim h

-- Comentario de JA: La demostración anterior se puede factorizar como
-- se muestra a continuación.

-- Proof 3
example : False → P :=
  fun h => False.elim h

-- Proof 4 (Automatic)
example : False → P := by
  intro hF
  -- hF : False
  -- ⊢ P
  contradiction

-- Proof 5 (Balanced)
example : False → P := by
  intro hF
  -- hF : False
  -- ⊢ P
  exfalso
  -- ⊢ False
  assumption

-- Comentario de JA: A continuación se muestran otras posibles
-- demostraciones.

-- Proof 6
example : False → P := by
  tauto

-- Proof 7
example : False → P := by
  simp only [false_implies]

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    True → (False → (True → (False → (True → False))))
-- ---------------------------------------------------------------------

-- Proof 1 (Detailed)
example : True → (False → (True → (False → (True → False)))) := by
  intro _hT hF1 _hT2 _hF2 _hT3
  -- _hT : True
  -- hF1 : False
  -- _hT2 : True
  -- _hF2 : False
  -- _hT3 : True
  -- ⊢ False
  exact hF1

-- Comentario de JA: La demostración anterior se puede refactorizar como
-- se muestra a continuación.

-- Proof 2
example : True → (False → (True → (False → (True → False)))) :=
  fun _ h _ _ _ => h

-- Proof 3 (Automatic)
example : True → False → True → False → True → False := by
  trivial

-- Proof 4 (Balanced)
example : True → False → True → False → True → False := by
  intro _hT _hF1 _hT2 hF2 _hT3
  -- _hT : True
  -- _hF1 : False
  -- _hT2 : True
  -- hF2 : False
  -- _hT3 : True
  -- ⊢ False
  assumption

-- Comentario de JA: Otras posibles demostraciones se muestran a
-- continuación

-- Proof 5
example : True → False → True → False → True → False := by
  decide

-- Proof 6
example : True → False → True → False → True → False := by
  tauto

-- ---------------------------------------------------------------------
-- Exercise 8. Prove that
--    P → ((P → False) → False)
-- ---------------------------------------------------------------------

-- Proof 1 (Detailed)
example : P → (P → False) → False := by
  intro hP hPF
  -- hP : P
  -- hPF : P → False
  -- ⊢ False
  apply hPF
  -- ⊢ P
  exact hP

-- Comentario de JA: La demostración anterior se ouede refactorizar como
-- se muestra a continuación.

-- Proof 2
example : P → (P → False) → False :=
  fun hP hPF => hPF hP

-- Proof 2 (Automatic)
example : P → (P → False) → False := by
  intro hP hPF
  -- hPF : P → False
  -- ⊢ False
  contradiction

-- Proof 3 (Balanced)
example : P → (P → False) → False := by
  intro hP hPF
  -- hP : P
  -- hPF : P → False
  -- ⊢ False
  apply hPF at hP
  -- hP : False
  exact hP

-- Comentario de JA: Se puede demostrar automáticamente como se muestra
-- a continuación.

-- Proof 4
example : P → (P → False) → False := by
  tauto

-- Example 9: Proving (P → False) → P → Q

--Proof 1 (Detailed)
example : (P → False) → P → Q := by
  intro hPF hP
  exfalso
  apply hPF
  exact hP

--Proof 2 (Automatic)
example : (P → False) → P → Q := by
  intro hPF hP
  contradiction

--Proof 3 (Balanced)
example : (P → False) → P → Q := by
  intro hPF hP
  apply hPF at hP
  contradiction


-- Example 10: Proving (True → False) → P

--Proof 1 (Detailed)
example : (True → False) → P := by
  intro hTF
  exfalso
  apply hTF
  exact True.intro

--Proof 2 (Automatic)
example : (True → False) → P := by
  intro hTF
  contradiction

--Proof 3 (Balanced)
example : (True → False) → P := by
  intro hTF
  exfalso
  trivial

-- Comentario de JA: He puesto como anónimas las variables no usadas.
