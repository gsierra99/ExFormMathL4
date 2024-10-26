-- C01_Logic/Pset6.lean
-- Problem set 6: The disjunction.
-- Gabriel Sierra Gallego.
-- Seville, October 26, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with the disjunction in
-- Lean4.
--
-- It is based on [Section01logic/Sheet4.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

variable (P Q R S : Prop)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    P → P ∨ Q
-- ---------------------------------------------------------------------

-- Proof 1
example : P → P ∨ Q := by
  intro hP
  -- hP : P
  -- ⊢ P ∨ Q
  left
  -- ⊢ P
  exact hP

-- Proof 2
example : P → P ∨ Q := by
  tauto

-- Proof 3
example : P → P ∨ Q := by
  intro hP
  -- hP : P
  -- ⊢ P ∨ Q
  exact Or.inl hP

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P → P ∨ Q :=
  fun hP => Or.inl hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P → P ∨ Q :=
  Or.inl

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    Q → P ∨ Q
-- ---------------------------------------------------------------------

-- Proof 1
example : Q → P ∨ Q := by
  intro hQ
  -- hQ : Q
  -- ⊢ P ∨ Q
  right
  -- ⊢ Q
  exact hQ

-- Proof 2
example : Q → P ∨ Q := by
  tauto

-- Proof 3
example : Q → P ∨ Q := by
  intro hQ
  -- hQ : Q
  -- ⊢ P ∨ Q
  exact Or.inr hQ

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : Q → P ∨ Q :=
  fun hQ => Or.inr hQ

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : Q → P ∨ Q :=
  Or.inr

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    P ∨ Q → ((P → R) → ((Q → R) → R))
-- ---------------------------------------------------------------------

-- Proof 1
example : P ∨ Q → ((P → R) → ((Q → R) → R)) := by
  intro hPoQ hPR hQR
  -- hPoQ : P ∨ Q
  -- hPR : P → R
  -- hQR : Q → R
  -- ⊢ R
  cases' hPoQ with hP hQ
  . -- hP : P
    apply hPR at hP
    -- hP : R
    exact hP
  . -- hQ : Q
    apply hQR at hQ
    -- hQ : R
    exact hQ

-- Proof 2
example : P ∨ Q → (P → R) → (Q → R) → R := by
  tauto

-- Proof 3
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  -- hPoQ : P ∨ Q
  -- hPR : P → R
  -- hQR : Q → R
  -- ⊢ R
  cases' hPoQ with hP hQ
  . -- hP : P
    exact hPR hP
  . -- hQ : Q
    exact hQR hQ

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (hP | hQ) hPR hQR
  -- hPR : P → R
  -- hQR : Q → R
  -- ⊢ R
  . -- hP : P
    exact hPR hP
  . -- hQ : Q
    exact hQR hQ

-- Comentario de JA: Se puede demostrar con Or.elim como se muestra a
-- continuación.

-- Proof 5
example : P ∨ Q → (P → R) → (Q → R) → R :=
  Or.elim

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    P ∨ Q → Q ∨ P
-- ---------------------------------------------------------------------

-- Proof 1
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  -- hPoQ : P ∨ Q
  -- ⊢ Q ∨ P
  cases' hPoQ with hP hQ
  . -- hP : P
    right
    -- ⊢ P
    exact hP
  . -- hQ : Q
    left
    -- ⊢ Q
    exact hQ

-- Proof 2
example : P ∨ Q → Q ∨ P := by
  tauto

-- Proof 3
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  -- hPoQ : P ∨ Q
  -- ⊢ Q ∨ P
  cases' hPoQ with hP hQ
  . -- hP : P
    exact Or.inr hP
  . -- hQ : Q
    exact Or.inl hQ

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P ∨ Q → Q ∨ P := by
  rintro (hP | hQ)
  -- ⊢ Q ∨ P
  . -- hP : P
    exact Or.inr hP
  . -- hQ : Q
    exact Or.inl hQ

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P ∨ Q → Q ∨ P := by
  apply Or.rec
  . -- P → Q ∨ P
    exact Or.inr
  . -- ⊢ Q → Q ∨ P
    exact Or.inl

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : P ∨ Q → Q ∨ P :=
  Or.rec Or.inr Or.inl

-- Comentario de JA: La 6ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : P ∨ Q → Q ∨ P :=
  .rec .inr .inl

-- Comentario de JA: Se puede demostrar con Or.symm como se muestra a
-- continuación.

-- Proof 8
example : P ∨ Q → Q ∨ P :=
  Or.symm

-- Example 5: (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R

-- Detailed proof
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro hPoQoR
  cases' hPoQoR with hPoQ hR
  cases' hPoQ with hP hQ
  left
  exact hP
  right
  left
  exact hQ
  right
  right
  exact hR
  intro hPoQoR
  cases' hPoQoR with hP hQoR
  left
  left
  exact hP
  cases' hQoR with hQ hR
  left
  right
  exact hQ
  right
  exact hR

-- Automatic proof
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  tauto

-- Balanced proof
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  -- Forward direction
  intro hPoQoR
  cases' hPoQoR with hPQ hR
  cases' hPQ with hP hQ
  exact Or.inl hP
  exact Or.inr (Or.inl hQ)
  exact Or.inr (Or.inr hR)
  -- Backward direction
  intro hPoQoR
  cases' hPoQoR with hP hQoR
  exact Or.inl (Or.inl hP)
  cases' hQoR with hQ hR
  exact Or.inl (Or.inr hQ)
  exact Or.inr hR


-- Example 6: (P → R) → (Q → S) → P ∨ Q → R ∨ S

-- Detailed proof
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  cases' hPoQ with hP hQ
  apply hPR at hP
  left
  exact hP
  apply hQS at hQ
  right
  exact hQ

-- Automatic proof
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  tauto

-- Balanced proof
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  cases' hPoQ with hP hQ
  exact Or.inl (hPR hP)
  exact Or.inr (hQS hQ)


-- Example 7: (P → Q) → P ∨ R → Q ∨ R

-- Detailed proof
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  cases' hPoR with hP hR
  apply hPQ at hP
  left
  exact hP
  right
  exact hR

-- Automatic proof
example : (P → Q) → P ∨ R → Q ∨ R := by
  tauto

-- Balanced proof
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  cases' hPoR with hP hR
  exact Or.inl (hPQ hP)
  exact Or.inr hR

-- Example 8: (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S)

-- Detailed proof
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPiffR hQiffS
  constructor
  intro hPoQ
  cases' hPoQ with hP hQ
  cases' hPiffR with hPR hRP
  apply hPR at hP
  left
  exact hP
  cases' hQiffS with hQS hSQ
  apply hQS at hQ
  right
  exact hQ
  intro hRoS
  cases' hRoS with hR hS
  cases' hPiffR with hPR hRP
  apply hRP at hR
  left
  exact hR
  cases' hQiffS with hQS hSQ
  apply hSQ at hS
  right
  exact hS

-- Automatic proof
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  tauto

-- Balanced proof
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
  by
  intro h1 h2
  rw [h1, h2]


-- Example 9: ¬(P ∨ Q) ↔ ¬P ∧ ¬Q

-- Detailed proof
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro hPoQ
  constructor
  intro hP
  apply hPoQ
  left
  exact hP
  intro hQ
  apply hPoQ
  right
  exact hQ
  intro hPAnQ
  intro hPoQ
  cases' hPAnQ with hP hQ
  cases' hPoQ with hP hQ
  contradiction
  contradiction


-- Automatic proof
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  tauto

-- Balanced proof
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro hPoQ
  exact ⟨fun hP => hPoQ (Or.inl hP), fun hQ => hPoQ (Or.inr hQ)⟩
  intro hPynQ
  intro hPoQ
  cases' hPoQ with hP hQ
  exact hPynQ.left hP
  exact hPynQ.right hQ

-- Example 10: ¬(P ∧ Q) ↔ ¬P ∨ ¬Q

-- Detailed proof
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by

  sorry

-- Automatic proof
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  tauto

-- Balanced proof
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      exact ⟨hP, hQ⟩
    · left
      exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · contradiction
    · apply hnQ; exact hQ
