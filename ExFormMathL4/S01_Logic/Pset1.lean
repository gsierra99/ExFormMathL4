-- S01_Logic/Pset1.lean
-- Problem set 1: The implication.
-- Gabriel Sierra Gallego.
-- Seville, October 1, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we begin the study of logic by considering
-- proofs where the only connective used is the implication.
--
-- It is based on [Section01logic//Sheet1.lean](https://tinyurl.com/23vjltb2)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic
variable (P Q R S T : Prop)

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    {P, Q, R} ⊢ P
-- ---------------------------------------------------------------------

-- Proof 1
example
  (hP : P)
  (_hQ : Q)
  (_hR : R)
  : P :=
by
  exact hP

-- Proof 2
example
  (hP : P)
  (_hQ : Q)
  (_hR : R)
  : P :=
hP

-- Proof 3
example
  (hP : P)
  (_hQ : Q)
  (_hR : R)
  : P :=
by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    {P, Q, R} ⊢ P
-- ---------------------------------------------------------------------

-- Proof 1
example
  (fish : P)
  (_giraffe : Q)
  (_dodecahedron : R)
  : P :=
by
  exact fish

-- Proof 2
example
  (fish : P)
  (_giraffe : Q)
  (_dodecahedron : R)
  : P :=
fish

-- Proof 3
example
  (fish : P)
  (_giraffe : Q)
  (_dodecahedron : R)
  : P :=
by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    Q ⊢ P → Q
-- ---------------------------------------------------------------------

-- Proof 1
example
  (hQ : Q)
  : P → Q :=
by
  intro _h
  -- _h : P
  -- ⊢ Q
  exact hQ

-- Proof 2
example
  (hQ : Q)
  : P → Q :=
fun _h ↦ hQ

-- Proof 3
example
  (hQ : Q)
  : P → Q :=
by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    {P → Q, P} ⊢ Q
-- ---------------------------------------------------------------------

-- Proof 1
example
  (h : P → Q)
  (hP : P)
  : Q :=
by
  apply h at hP
  -- hP : Q
  exact hP

-- Proof 2
example
  (h : P → Q)
  (hP : P)
  : Q :=
by
  apply h
  -- ⊢ P
  exact hP

-- Proof 3
example
  (h : P → Q)
  (hP : P)
  : Q :=
h hP

-- Proof 4
example
  (h : P → Q)
  (hP : P)
  : Q :=
by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ P → P
-- ---------------------------------------------------------------------

-- Proof 1
example :
  P → P :=
by
  intro hP
  -- hP : P
  -- ⊢ P
  exact hP

-- Proof 2
example :
  P → P :=
fun hP ↦ hP

-- Proof 3
example :
  P → P :=
by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ P → (Q → P)
-- ---------------------------------------------------------------------

-- Proof 1
example :
  P → (Q → P) :=
by
  intro hP _hQ
  -- hP : P
  -- _hQ : Q
  -- ⊢ P
  exact hP

-- Proof 2
example :
  P → (Q → P) :=
fun hP _hQ => hP

-- Proof 3
example :
  P → (Q → P) :=
by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ P → ((P → Q) → Q)
-- ---------------------------------------------------------------------

-- Proof 1
example : P → (P → Q) → Q := by
  intro (hP : P) (hPimpQ : P → Q)
  -- hP : P
  -- hPimpQ : P → Q
  -- ⊢ Q
  apply hPimpQ at hP
  -- hP : Q
  exact hP

-- Proof 2
example : P → (P → Q) → Q := by
  intro hP hPQ
  -- hP : P
  -- hPQ : P → Q
  -- ⊢ Q
  apply hPQ
  -- ⊢ P
  exact hP

-- Proof 3
example : P → (P → Q) → Q :=
fun hP hPQ => hPQ hP

-- Proof 4
example : P → (P → Q) → Q := by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ (P → Q) → (Q → R) → P → R
-- ---------------------------------------------------------------------

-- Proof 1
example : (P → Q) → (Q → R) → P → R := by
  intro (hPimpQ : P → Q) (hQimpR : Q → R) (hP : P)
  -- hPimpQ : P → Q
  -- hQimpR : Q → R
  -- hP : P
  -- ⊢ R
  apply hPimpQ at hP
  -- hP : Q
  apply hQimpR at hP
  -- hP : R
  exact hP

-- Proof 2
example : (P → Q) → (Q → R) → P → R :=
by
  intro hPQ hQR hP
  -- hPQ : P → Q
  -- hQR : Q → R
  -- hP : P
  -- ⊢ R
  apply hQR
  -- ⊢ Q
  apply hPQ
  -- ⊢ P
  exact hP

-- Proof 3
example : (P → Q) → (Q → R) → P → R :=
fun hPQ hQR hP => hQR (hPQ hP)

-- Proof 4
example : (P → Q) → (Q → R) → P → R :=
by
  intro hPQ hQR hP
  -- hPQ : P → Q
  -- hQR : Q → R
  -- hP : P
  -- ⊢ R
  have hQ : Q := hPQ hP
  show R
  exact hQR hQ

-- Proof 5
example : (P → Q) → (Q → R) → P → R :=
by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ (P → Q → R) → (P → Q) → P → R
-- ---------------------------------------------------------------------

-- Proof 1
example : (P → Q → R) → (P → Q) → P → R := by
  intro (hPQR : P → Q → R) (hPQ : P → Q) (hP : P)
  -- hPQR : P → Q → R
  -- hPQ : P → Q
  -- hP : P
  -- ⊢ R
  apply hPQR
  . -- ⊢ P
    exact hP
  . -- ⊢ Q
    apply hPQ at hP
    -- hP : Q
    exact hP

-- Proof 2
example : (P → Q → R) → (P → Q) → P → R := by
  intro hPQR hPQ hP
  -- hPQR : P → Q → R
  -- hPQ : P → Q
  -- hP : P
  -- ⊢ R
  apply hPQR
  . -- ⊢ P
    exact hP
  . -- ⊢ Q
    apply hPQ
    -- ⊢ P
    exact hP

-- Proof 3
example : (P → Q → R) → (P → Q) → P → R :=
fun hPQR hPQ hP => hPQR hP (hPQ hP)

-- Proof 4
example : (P → Q → R) → (P → Q) → P → R := by
  intro hPQR hPQ hP
  -- hPQR : P → Q → R
  -- hPQ : P → Q
  -- hP : P
  -- ⊢ R
  have hQ : Q := hPQ hP
  have hQR : Q → R := hPQR hP
  show R
  exact hQR hQ

-- Proof 5
example : (P → Q → R) → (P → Q) → P → R := by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ (P → R) → (S → Q) → (R → T) → (Q → R) → S → T
-- ---------------------------------------------------------------------

-- Proof 1
example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro (_hPR : P → R) (hSQ : S → Q) (hRT : R → T) (hQR : Q → R) (hS : S)
  -- _hPR : P → R
  -- hSQ : S → Q
  -- hRT : R → T
  -- hQR : Q → R
  -- hS : S
  -- ⊢ T
  apply hSQ at hS
  -- hS : Q
  apply hQR at hS
  -- hS : R
  apply hRT at hS
  -- hS : T
  exact hS

-- Proof 2
example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro _hPR hSQ hRT hQR hS
  -- _hPR : P → R
  -- hSQ : S → Q
  -- hRT : R → T
  -- hQR : Q → R
  -- hS : S
  -- ⊢ T
  apply hRT
  -- ⊢ R
  apply hQR
  -- ⊢ Q
  apply hSQ
  -- ⊢ S
  exact hS

-- Proof 3
example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T :=
  fun _hPR hSQ hRT hQR hS => hRT (hQR (hSQ hS))

-- Proof 4
example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  intro _hPR hSQ hRT hQR hS
  -- _hPR : P → R
  -- hSQ : S → Q
  -- hRT : R → T
  -- hQR : Q → R
  -- hS : S
  -- ⊢ T
  have hQ : Q := hSQ hS
  have hR : R := hQR hQ
  show T
  exact hRT hR

-- Proof 5
example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T := by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ (P → Q) → ((P → Q) → P) → Q
-- ---------------------------------------------------------------------

-- Proof 1
example : (P → Q) → ((P → Q) → P) → Q :=
by
  intro (hPQ : P → Q) (hPQP : (P → Q) → P)
  -- hPQ : P → Q
  -- hPQP : (P → Q) → P
  -- ⊢ Q
  apply hPQ
  -- ⊢ P
  apply hPQP at hPQ
  -- hPQ : P
  exact hPQ

-- Proof 2
example : (P → Q) → ((P → Q) → P) → Q :=
by
  intro hPQ hPQP
  -- hPQ : P → Q
  -- hPQP : (P → Q) → P
  -- ⊢ Q
  apply hPQ
  -- ⊢ P
  apply hPQP
  -- ⊢ P → Q
  exact hPQ

-- Proof 3
example : (P → Q) → ((P → Q) → P) → Q :=
fun hPQ hPQP => hPQ (hPQP hPQ)

-- Proof 4
example : (P → Q) → ((P → Q) → P) → Q :=
by
  intro hPQ hPQP
  -- hPQ : P → Q
  -- hPQP : (P → Q) → P
  -- ⊢ Q
  have hP : P := hPQP hPQ
  show Q
  exact hPQ hP

-- Proof 5
example : (P → Q) → ((P → Q) → P) → Q :=
by
  tauto

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P
-- ---------------------------------------------------------------------

example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P := by
  sorry

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ ((Q → P) → P) → (Q → R) → (R → P) → P
-- ---------------------------------------------------------------------

example : ((Q → P) → P) → (Q → R) → (R → P) → P := by
  sorry

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ (((P → Q) → Q) → Q) → P → Q
-- ---------------------------------------------------------------------

example : (((P → Q) → Q) → Q) → P → Q := by
  sorry

-- ---------------------------------------------------------------------
-- Exercise. Prove that
--    ⊢ (((P → Q → Q) → (P → Q) → Q) → R) →
--      ((((P → P) → Q) → P → P → Q) → R) →
--      (((P → P → Q) → (P → P) → Q) → R) →
--      R
-- ---------------------------------------------------------------------

example :
    (((P → Q → Q) → (P → Q) → Q) → R) →
    ((((P → P) → Q) → P → P → Q) → R) →
    (((P → P → Q) → (P → P) → Q) → R) →
    R := by
  sorry
