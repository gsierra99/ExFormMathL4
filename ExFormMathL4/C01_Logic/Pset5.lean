-- C01_Logic/Pset5.lean
-- Problem set 5: The bi-implication.
-- Gabriel Sierra Gallego.
-- Seville, October 23, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with the bi-implication in
-- Lean4.
--
-- It is based on [Section01logic/Sheet4.lean](https://tinyurl.com/24urpkse)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

variable (P Q R S : Prop)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    P ↔ P
-- ---------------------------------------------------------------------

-- Proof 1
example : P ↔ P := by
  constructor
  . -- ⊢ P → P
    intro hP
    -- hP : P
    -- ⊢ P
    exact hP
  . -- ⊢ P → P
    intro hP
    -- hP : P
    -- ⊢ P
    exact hP

-- Proof 2
example : P ↔ P := by
  tauto

-- Proof 3
example : P ↔ P := by
  constructor
  . -- ⊢ P → P
    exact fun a => a
  . -- ⊢ P → P
    exact fun a => a

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P ↔ P :=
  ⟨fun a => a, fun a => a⟩

-- Comentario de JA: Se puede demostrar con Iff.refl como se muestra a
-- continuación.

-- Proof 5
example : P ↔ P :=
  Iff.refl P

-- Comentario de JA: Se puede demostrar con rfl como se muestra a
-- continuación.

-- Proof 6
example : P ↔ P := by
  rfl

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    (P ↔ Q) → (Q ↔ P)
-- ---------------------------------------------------------------------

-- Proof 1
example : (P ↔ Q) → (Q ↔ P) := by
  intro hPiffQ
  -- hPiffQ : P ↔ Q
  -- ⊢ Q ↔ P
  cases' hPiffQ with hPQ hQP
  -- hPQ : P → Q
  -- hQP : Q → P
  constructor
  . -- ⊢ Q → P
    intro hQ
    -- hQ : Q
    -- ⊢ P
    apply hQP
    -- ⊢ Q
    exact hQ
  . -- ⊢ P → Q
    intro hP
    -- hP : P
    -- ⊢ Q
    apply hPQ
    -- ⊢ P
    exact hP

-- Proof 2
example : (P ↔ Q) → (Q ↔ P) := by
  tauto

-- Proof 3
example : (P ↔ Q) → (Q ↔ P) := by
  intro hPiffQ
  -- hPiffQ : P ↔ Q
  -- ⊢ Q ↔ P
  cases' hPiffQ with hPQ hQP
  -- hPQ : P → Q
  -- hQP : Q → P
  exact ⟨hQP, hPQ⟩

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : (P ↔ Q) → (Q ↔ P) := by
  intro hPiffQ
  -- hPiffQ : P ↔ Q
  -- ⊢ Q ↔ P
  constructor
  . -- ⊢ Q → P
    exact hPiffQ.mpr
  . -- ⊢ P → Q
    exact hPiffQ.mp

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : (P ↔ Q) → (Q ↔ P) := by
  intro hPiffQ
  -- hPiffQ : P ↔ Q
  -- ⊢ Q ↔ P
  exact ⟨hPiffQ.mpr, hPiffQ.mp⟩

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : (P ↔ Q) → (Q ↔ P) :=
  fun hPiffQ => ⟨hPiffQ.mpr, hPiffQ.mp⟩

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : (P ↔ Q) → (Q ↔ P) := by
  rintro ⟨hPQ, hQP⟩
  -- hPQ : P → Q
  -- hQP : Q → P
  exact ⟨hQP, hPQ⟩

-- Comentario de JA: La 7ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 8
example : (P ↔ Q) → (Q ↔ P) :=
  fun ⟨hPQ, hQP⟩ => ⟨hQP, hPQ⟩

-- Comentario de JA: Se puede demostrar con rw como se muestra a
-- continuación.

-- Proof 9
example : (P ↔ Q) → (Q ↔ P) := by
  intro hPiffQ
  -- hPiffQ : P ↔ Q
  -- ⊢ Q ↔ P
  rw [hPiffQ]

-- Comentario de JA: Se puede demostrar con Iff.symm como se muestra a
-- continuación.

-- Proof 10
example : (P ↔ Q) → (Q ↔ P) :=
  Iff.symm

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--   (P ↔ Q) ↔ (Q ↔ P)
-- ---------------------------------------------------------------------

-- Proof 1
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  . -- ⊢ (P ↔ Q) → (Q ↔ P)
    intro hPiffQ
    -- hPiffQ : P ↔ Q
    -- ⊢ Q ↔ P
    cases' hPiffQ with hPQ hQP
    -- hPQ : P → Q
    -- hQP : Q → P
    constructor
    . -- ⊢ Q → P
      intro hQ
      -- hQ : Q
      -- ⊢ P
      apply hQP
      -- ⊢ Q
      exact hQ
    . -- ⊢ P → Q
      intro hP
      -- hP : P
      -- ⊢ Q
      apply hPQ
      -- ⊢ P
      exact hP
  . -- ⊢ (Q ↔ P) → (P ↔ Q)
    intro hQiffP
    -- hQiffP : Q ↔ P
    -- ⊢ P ↔ Q
    cases' hQiffP with hQP hPQ
    -- hQP : Q → P
    -- hPQ : P → Q
    constructor
    . -- ⊢ P → Q
      intro hP
      -- hP : P
      -- ⊢ Q
      apply hPQ
      -- ⊢ P
      exact hP
    . -- ⊢ Q → P
      intro hQ
      -- hQ : Q
      -- ⊢ P
      apply hQP
      -- ⊢ Q
      exact hQ

-- Proof 2
example : (P ↔ Q) ↔ (Q ↔ P) := by
  tauto

-- Proof 3
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  . -- ⊢ (P ↔ Q) → (Q ↔ P)
    intro hPiffQ
    -- hPiffQ : P ↔ Q
    -- ⊢ Q ↔ P
    cases' hPiffQ with hPQ hQP
    -- hPQ : P → Q
    -- hQP : Q → P
    exact ⟨hQP, hPQ⟩
  . -- ⊢ (Q ↔ P) → (P ↔ Q)
    intro hQiffP
    -- hQiffP : Q ↔ P
    -- ⊢ P ↔ Q
    cases' hQiffP with hQP hPQ
    -- hQP : Q → P
    -- hPQ : P → Q
    exact ⟨hPQ, hQP⟩

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  . -- ⊢ (P ↔ Q) → (Q ↔ P)
    intro hPiffQ
    -- hPiffQ : P ↔ Q
    -- ⊢ Q ↔ P
    exact ⟨hPiffQ.mpr, hPiffQ.mp⟩
  . -- ⊢ (Q ↔ P) → (P ↔ Q)
    intro hQiffP
    -- hQiffP : Q ↔ P
    -- ⊢ P ↔ Q
    exact ⟨hQiffP.mpr, hQiffP.mp⟩

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : (P ↔ Q) ↔ (Q ↔ P) :=
  ⟨fun hPiffQ => ⟨hPiffQ.mpr, hPiffQ.mp⟩,
   fun hQiffP => ⟨hQiffP.mpr, hQiffP.mp⟩⟩

-- Comentario de JA: La 6ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : (P ↔ Q) ↔ (Q ↔ P) :=
  ⟨fun ⟨hPQ, hQP⟩ => ⟨hQP, hPQ⟩,
   fun ⟨hQP, hPQ⟩ => ⟨hPQ, hQP⟩⟩

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  . -- ⊢ (P ↔ Q) → (Q ↔ P)
    rintro ⟨hPQ, hQP⟩
    -- hPQ : P → Q
    -- hQP : Q → P
    -- ⊢ Q ↔ P
    exact ⟨hQP, hPQ⟩
  . -- ⊢ (Q ↔ P) → (P ↔ Q)
    rintro ⟨hQP, hPQ⟩
    -- hQP : Q → P
    -- hPQ : P → Q
    -- ⊢ P ↔ Q
    exact ⟨hPQ, hQP⟩

-- Comentario de JA: Se puede demostrar usando rw como se muestra a
-- continuación.

-- Proof 7
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  . -- ⊢ (P ↔ Q) → (Q ↔ P)
    intro h
    -- h : P ↔ Q
    -- ⊢ Q ↔ P
    rw [h]
  . -- ⊢ (Q ↔ P) → (P ↔ Q)
    intro h
    -- h : Q ↔ P
    -- ⊢ P ↔ Q
    rw [h]

-- Comentario de JA: La 7ª demostración se puede simplificar usando <;> como se
-- muestra a continuación.

-- Proof 8
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;>
  . intro h
    rw [h]

-- Comentario de JA: Se puede demostrar con Iff.comm como se muestra a
-- continuación.

-- Proof 9
example : (P ↔ Q) ↔ (Q ↔ P) :=
  Iff.comm

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    (P ↔ Q) → ((Q ↔ R) → (P ↔ R))
-- ---------------------------------------------------------------------

-- Proof 1
example : (P ↔ Q) → ((Q ↔ R) → (P ↔ R)) := by
  intro hPiffQ hQiffR
  -- hPiffQ : P ↔ Q
  -- hQiffR : Q ↔ R
  -- ⊢ P ↔ R
  cases' hPiffQ with hPQ hQP
  -- hPQ : P → Q
  -- hQP : Q → P
  cases' hQiffR with hQR hRQ
  -- hQR : Q → R
  -- hRQ : R → Q
  constructor
  . -- ⊢ P → R
    intro hP
    -- hP : P
    -- ⊢ R
    apply hQR
    -- ⊢ Q
    apply hPQ
    -- ⊢ P
    exact hP
  . -- ⊢ R → P
    intro hR
    -- hR : R
    -- ⊢ P
    apply hQP
    -- ⊢ Q
    apply hRQ
    -- ⊢ R
    exact hR

-- Proof 2
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  tauto

-- Proof 3
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPiffQ hQiffR
  -- hPiffQ : P ↔ Q
  -- hQiffR : Q ↔ R
  -- ⊢ P ↔ R
  cases' hPiffQ with hPQ hQP
  -- hPQ : P → Q
  -- hQP : Q → P
  cases' hQiffR with hQR hRQ
  -- hQR : Q → R
  -- hRQ : R → Q
  exact ⟨fun hP => hQR (hPQ hP), fun hR => hQP (hRQ hR)⟩

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  rintro ⟨hPQ, hQP⟩ ⟨hQR, hRQ⟩
  -- hPQ : P → Q
  -- hQP : Q → P
  -- hQR : Q → R
  -- hRQ : R → Q
  -- ⊢ P ↔ R
  exact ⟨fun hP => hQR (hPQ hP), fun hR => hQP (hRQ hR)⟩

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  fun ⟨hPQ, hQP⟩ ⟨hQR, hRQ⟩ => ⟨fun hP => hQR (hPQ hP),
                                fun hR => hQP (hRQ hR)⟩

-- Comentario de JA: Se puede demostrar con rw como se muestra a
-- continuación.

-- Proof 6
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPiffQ hQiffR
  -- hPiffQ : P ↔ Q
  -- hQiffR : Q ↔ R
  -- ⊢ P ↔ R
  rw [hPiffQ]
  -- ⊢ Q ↔ R
  assumption

-- Comentario de JA: La 5ª demostración se puede simplificar usando rwa
-- como se muestra a continuación.

-- Proof 7
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPiffQ hQiffR
  -- hPiffQ : P ↔ Q
  -- hQiffR : Q ↔ R
  -- ⊢ P ↔ R
  rwa [hPiffQ]

-- Comentario de JA: Se puede demostrar con Iff.trans como se muestra a
-- continuación.

-- Proof 8
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  Iff.trans

-- Example 5: P ∧ Q ↔ Q ∧ P

-- Detailed proof
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro hPyQ
  cases' hPyQ with hP hQ
  constructor
  exact hQ
  exact hP
  intro hQyP
  cases' hQyP with hQ hP
  constructor
  exact hP
  exact hQ

-- Automatic proof
example : P ∧ Q ↔ Q ∧ P := by
  tauto

-- Balanced proof
example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro hPyQ
  exact ⟨hPyQ.right, hPyQ.left⟩
  intro hQyP
  exact ⟨hQyP.right, hQyP.left⟩


-- Example 6: (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R

-- Detailed proof
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

-- Automatic proof
example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  tauto

-- Balanced proof
example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro hPyQyR
  exact ⟨hPyQyR.left.left, hPyQyR.left.right, hPyQyR.right⟩
  intro hPyQyR
  exact ⟨⟨hPyQyR.left, hPyQyR.right.left⟩, hPyQyR.right.right⟩


-- Example 7: P ↔ P ∧ True

-- Detailed proof
example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  exact hP
  trivial
  intro hPyT
  cases' hPyT with hP hT
  exact hP

-- Automatic proof
example : P ↔ P ∧ True := by
  tauto

-- Balanced proof
example : P ↔ P ∧ True := by
  constructor
  intro hP
  exact ⟨hP, trivial⟩
  intro hPyT
  exact hPyT.left


-- Example 8: False ↔ P ∧ False

-- Detailed proof
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

-- Automatic proof
example : False ↔ P ∧ False := by
  tauto

-- Balanced proof
example : False ↔ P ∧ False := by
  constructor
  intro hF
  exact ⟨hF.elim, hF⟩
  intro hPyF
  exact hPyF.right.elim


-- Example 9: (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S)

-- Detailed proof
example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPiffQ hRiffS
  cases' hPiffQ with hPQ hQP
  cases' hRiffS with hRS hSR
  constructor
  intro hPyR
  cases' hPyR with hP hR
  constructor
  apply hPQ
  exact hP
  apply hRS
  exact hR
  intro hQyS
  cases' hQyS with hQ hS
  constructor
  apply hQP
  exact hQ
  apply hSR
  exact hS

-- Automatic proof
example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  tauto

-- Balanced proof
example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPiffQ hRiffS
  cases' hPiffQ with hPQ hQP
  cases' hRiffS with hRS hSR
  exact ⟨fun hPyR => ⟨hPQ hPyR.left, hRS hPyR.right⟩, fun hQyS => ⟨hQP hQyS.left, hSR hQyS.right⟩⟩


-- Example 10: ¬(P ↔ ¬P)

-- Detailed proof
example : ¬(P ↔ ¬P) := by
  intro hPiffnP
  cases' hPiffnP with hPtonP hnPtoP
  have hP : P := by
    apply hnPtoP
    intro hP
    exact hPtonP hP hP
  exact hPtonP hP hP

-- Automatic proof
example : ¬(P ↔ ¬P) := by
  tauto

-- Balanced proof
example : ¬(P ↔ ¬P) := by
  intro hPiffnP
  cases' hPiffnP with hPtonP hnPtoP
  have hP : P := hnPtoP (fun hP => hPtonP hP hP)
  exact hPtonP hP hP
