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


-- Example 1: Proving True

--Proof 1 (Detailed)
example : True := by
  exact True.intro

--Proof 2 (Automatic)
example : True := by
  trivial

--Proof 3 (Balanced)
example : True := by
  constructor

-- Example 2: Proving True → True

--Proof 1 (Detailed)
example : True → True := by
    intro hT
    exact hT

--Proof 2 (Automatic)
example : True → True := by
    trivial

--Proof 3 (Balanced)
example : True → True := by
    trivial



-- Example 3: Proving False → True

--Proof 1 (Detailed)
example : False → True := by
  intro hF
  exfalso
  exact hF

--Proof 2 (Automatic)
example : False → True := by
  trivial

--Proof 3 (Balanced)
example : False → True := by
  intro hF
  trivial


-- Example 4: Proving False → False

--Proof 1 (Detailed)
example : False → False := by
  intro hF
  exact hF

--Proof 2 (Automatic)
example : False → False := by
    trivial

--Proof 3 (Balanced)
example : False → False := by
  intro hF
  assumption


-- Example 5: Proving (True → False) → False

--Proof 1 (Detailed)
example : (True → False) → False := by
  intro hTF
  apply hTF
  exact True.intro

--Proof 2 (Automatic)
example : (True → False) → False := by
  intro hTF
  contradiction

--Proof 3 (Balanced)
example : (True → False) → False := by
  intro hTF
  apply hTF
  trivial


-- Example 6: Proving False → P

--Proof 1 (Detailed)
example : False → P := by
  intro hF
  exfalso
  exact hF

--Proof 2 (Automatic)
example : False → P := by
  intro hF
  contradiction

--Proof 3 (Balanced)
example : False → P := by
  intro hF
  exfalso
  assumption


-- Example 7: Proving True → False → True → False → True → False

--Proof 1 (Detailed)
example : True → False → True → False → True → False := by
  intro hT hF1 hT2 hF2 hT3
  exact hF1

--Proof 2 (Automatic)
example : True → False → True → False → True → False := by
  trivial

--Proof 3 (Balanced)
example : True → False → True → False → True → False := by
  intro hT hF1 hT2 hF2 hT3
  assumption


-- Example 8: Proving P → (P → False) → False

--Proof 1 (Detailed)
example : P → (P → False) → False := by
  intro hP hPF
  apply hPF
  exact hP

--Proof 2 (Automatic)
example : P → (P → False) → False := by
  intro hP hPF
  contradiction

--Proof 3 (Balanced)
example : P → (P → False) → False := by
  intro hP hPF
  apply hPF at hP
  exact hP


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
