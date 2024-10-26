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

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P ∨ Q → (P → R) → (Q → R) → R := by
  apply Or.rec
  . -- ⊢ P → (P → R) → (Q → R) → R
    rintro hP hPR -
    -- hP : P
    -- hPR : P → R
    -- ⊢ R
    exact hPR hP
  . -- ⊢ Q → (P → R) → (Q → R) → R
    rintro hQ - hQR
    -- hQ : Q
    -- hQR : Q → R
    -- ⊢ R
    exact hQR hQ

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : P ∨ Q → (P → R) → (Q → R) → R :=
  Or.rec (fun hP hPR _ => hPR hP)
         (fun hQ _ hQR => hQR hQ)

-- Comentario de JA: Se puede demostrar con Or.elim como se muestra a
-- continuación.

-- Proof 7
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

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R)
-- ---------------------------------------------------------------------

-- Proof 1
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  constructor
  . -- ⊢ (P ∨ Q) ∨ R → P ∨ Q ∨ R
    intro hPoQoR
    -- hPoQoR : (P ∨ Q) ∨ R
    -- ⊢ P ∨ Q ∨ R
    cases' hPoQoR with hPoQ hR
    . -- hPoQ : P ∨ Q
      cases' hPoQ with hP hQ
      . -- hP : P
        left
        -- ⊢ P
        exact hP
      . -- hQ : Q
        right
        -- ⊢ Q ∨ R
        left
        -- ⊢ Q
        exact hQ
    . -- hR : R
      right
      -- ⊢ Q ∨ R
      right
      -- ⊢ R
      exact hR
  . -- ⊢ P ∨ Q ∨ R → (P ∨ Q) ∨ R
    intro hPoQoR
    -- hPoQoR : P ∨ Q ∨ R
    -- ⊢ (P ∨ Q) ∨ R
    cases' hPoQoR with hP hQoR
    . -- hP : P
      left
      -- ⊢ P ∨ Q
      left
      -- ⊢ P
      exact hP
    . -- hQoR : Q ∨ R
      cases' hQoR with hQ hR
      . -- hQ : Q
        left
        -- ⊢ P ∨ Q
        right
        -- ⊢ Q
        exact hQ
      . -- hR : R
        right
        -- ⊢ R
        exact hR

-- Proof 2
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  tauto

-- Proof 3
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  . -- ⊢ (P ∨ Q) ∨ R → P ∨ Q ∨ R
    intro hPoQoR
    -- hPoQoR : (P ∨ Q) ∨ R
    -- ⊢ P ∨ Q ∨ R
    cases' hPoQoR with hPQ hR
    . -- hPQ : P ∨ Q
      cases' hPQ with hP hQ
      . -- hP : P
        exact Or.inl hP
      . -- hQ : Q
        exact Or.inr (Or.inl hQ)
    . -- hR : R
      exact Or.inr (Or.inr hR)
  . -- ⊢ P ∨ Q ∨ R → (P ∨ Q) ∨ R
    intro hPoQoR
    -- hPoQoR : P ∨ Q ∨ R
    -- ⊢ (P ∨ Q) ∨ R
    cases' hPoQoR with hP hQoR
    . -- hP : P
      exact Or.inl (Or.inl hP)
    . -- hQoR : Q ∨ R
      cases' hQoR with hQ hR
      . -- hQ : Q
        exact Or.inl (Or.inr hQ)
      . -- hR : R
        exact Or.inr hR

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  . -- ⊢ (P ∨ Q) ∨ R → P ∨ (Q ∨ R)
    rintro ((hP | hQ) | hR)
    . -- hP : P
      exact Or.inl hP
    . -- hQ : Q
      exact Or.inr (Or.inl hQ)
    . -- hR : R
      exact Or.inr (Or.inr hR)
  . -- ⊢ P ∨ (Q ∨ R) → (P ∨ Q) ∨ R
    rintro (hP | (hQ | hR))
    . -- hP : P
      exact Or.inl (Or.inl hP)
    . -- hQ : Q
      exact Or.inl (Or.inr hQ)
    . -- hR : R
      exact Or.inr hR

-- Comentario de JA: Se puede demostrar con or_assoc como se muestra a
-- continuación.

-- Proof 5
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
  or_assoc

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    (P → R) → ((Q → S) → (P ∨ Q → R ∨ S))
-- ---------------------------------------------------------------------

-- Proof 1
example : (P → R) → ((Q → S) → (P ∨ Q → R ∨ S)) := by
  intro hPR hQS hPoQ
  -- hPR : P → R
  -- hQS : Q → S
  -- hPoQ : P ∨ Q
  -- ⊢ R ∨ S
  cases' hPoQ with hP hQ
  . -- hP : P
    apply hPR at hP
    -- hP : R
    left
    -- ⊢ R
    exact hP
  . -- hQ : Q
    apply hQS at hQ
    -- hQ : S
    right
    -- ⊢ S
    exact hQ

-- Automatic proof
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  tauto

-- Proof 3
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  -- hPR : P → R
  -- hQS : Q → S
  -- hPoQ : P ∨ Q
  -- ⊢ R ∨ S
  cases' hPoQ with hP hQ
  . -- hP : P
    exact Or.inl (hPR hP)
  . -- hQ : Q
    exact Or.inr (hQS hQ)

-- Comentario de JA: La 3ª demostración se puede nodificar como se
-- muestra a continuación.

-- Proof 4
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  -- hPR : P → R
  -- hQS : Q → S
  -- hPoQ : P ∨ Q
  -- ⊢ R ∨ S
  apply Or.elim hPoQ
  . -- ⊢ P → R ∨ S
    exact fun hP => Or.inl (hPR hP)
  . -- ⊢ Q → R ∨ S
    exact fun hQ => Or.inr (hQS hQ)

-- Comentario de JA: La 4ª demostración se puede modificar como se
-- muestra a continuación.

-- Proof 5
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
  fun hPR hQS hPoQ => Or.elim hPoQ (fun hP => Or.inl (hPR hP))
                                   (fun hQ => Or.inr (hQS hQ))

-- Comentario de JA: La 5ª demostración se puede simplificar usando
-- composición de funciones como se muestra a continuación.

-- Proof 6
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
  fun hPR hQS hPoQ => Or.elim hPoQ (Or.inl ∘ hPR)
                                   (Or.inr ∘ hQS)

-- Comentario de JA: La 5ª demostración se puede simplificar usando
-- composición de funciones como se muestra a continuación.

-- Proof 7
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
  fun hPR hQS hPoQ => .elim hPoQ (.inl ∘ hPR)
                                 (.inr ∘ hQS)

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 8
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  rintro hPR hQS (hP | hQ)
  -- hPR : P → R
  -- hQS : Q → S
  -- ⊢ R ∨ S
  . -- hP : P
    exact Or.inl (hPR hP)
  . -- hQ : Q
    exact Or.inr (hQS hQ)

-- Comentario de JA: Se puede demostrar con Or.imp como se muestra a
-- continuación.

-- Proof 9
example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
  Or.imp

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    (P → Q) → (P ∨ R → Q ∨ R)
-- ---------------------------------------------------------------------

-- Proof 1
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  -- hPQ : P → Q
  -- hPoR : P ∨ R
  -- ⊢ Q ∨ R
  cases' hPoR with hP hR
  . -- hP : P
    apply hPQ at hP
    -- hP : Q
    left
    -- ⊢ Q
    exact hP
  . -- hR : R
    right
    -- ⊢ R
    exact hR

-- Proof 2
example : (P → Q) → P ∨ R → Q ∨ R := by
  tauto

-- Proof 3
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  -- hPQ : P → Q
  -- hPoR : P ∨ R
  -- ⊢ Q ∨ R
  cases' hPoR with hP hR
  . -- hP : P
    exact Or.inl (hPQ hP)
  . -- hR : R
    exact Or.inr hR

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : (P → Q) → P ∨ R → Q ∨ R := by
  rintro hPQ (hP | hR)
  -- hPQ : P → Q
  -- ⊢ Q ∨ R
  . -- hP : P
    exact Or.inl (hPQ hP)
  . -- hR : R
    exact Or.inr hR

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  -- hPQ : P → Q
  -- hPoR : P ∨ R
  -- ⊢ Q ∨ R
  apply Or.elim hPoR
  . -- ⊢ P → Q ∨ R
    exact fun hP => Or.inl (hPQ hP)
  . -- ⊢ R → Q ∨ R
    exact Or.inr

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ hPoR
  -- hPQ : P → Q
  -- hPoR : P ∨ R
  -- ⊢ Q ∨ R
  apply Or.elim hPoR
  . -- ⊢ P → Q ∨ R
    exact Or.inl ∘ hPQ
  . -- ⊢ R → Q ∨ R
    exact Or.inr

-- Comentario de JA: La 6ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : (P → Q) → P ∨ R → Q ∨ R :=
  fun hPQ hPoR => Or.elim hPoR (Or.inl ∘ hPQ) Or.inr

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
