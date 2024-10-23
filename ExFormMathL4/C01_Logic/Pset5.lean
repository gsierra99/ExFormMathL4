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


-- Example 1: P ↔ P

-- Detailed proof
example : P ↔ P := by
  constructor
  intro hP
  exact hP
  intro hP
  exact hP

-- Automatic proof
example : P ↔ P := by
  tauto

-- Balanced proof
example : P ↔ P := by
  constructor
  exact fun a => a
  exact fun a => a


-- Example 2: (P ↔ Q) → (Q ↔ P)

-- Detailed proof
example : (P ↔ Q) → (Q ↔ P) := by
  intro hPiffQ
  cases' hPiffQ with hPQ hQP
  constructor
  intro hQ
  apply hQP
  exact hQ
  intro hP
  apply hPQ
  exact hP

-- Automatic proof
example : (P ↔ Q) → (Q ↔ P) := by
  tauto

-- Balanced proof
example : (P ↔ Q) → (Q ↔ P) := by
  intro hPiffQ
  cases' hPiffQ with hPQ hQP
  exact ⟨hQP, hPQ⟩


-- Example 3: (P ↔ Q) ↔ (Q ↔ P)

-- Detailed proof
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hPiffQ
  cases' hPiffQ with hPQ hQP
  constructor
  intro hQ
  apply hQP
  exact hQ
  intro hP
  apply hPQ
  exact hP
  intro hQiffP
  cases' hQiffP with hQP hPQ
  constructor
  intro hP
  apply hPQ
  exact hP
  intro hQ
  apply hQP
  exact hQ

-- Automatic proof
example : (P ↔ Q) ↔ (Q ↔ P) := by
  tauto

-- Balanced proof
example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hPiffQ
  cases' hPiffQ with hPQ hQP
  exact ⟨hQP, hPQ⟩
  intro hQiffP
  cases' hQiffP with hQP hPQ
  exact ⟨hPQ, hQP⟩


-- Example 4: (P ↔ Q) → (Q ↔ R) → (P ↔ R)

-- Detailed proof
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPiffQ hQiffR
  cases' hPiffQ with hPQ hQP
  cases' hQiffR with hQR hRQ
  constructor
  intro hP
  apply hQR
  apply hPQ
  exact hP
  intro hR
  apply hQP
  apply hRQ
  exact hR

-- Automatic proof
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  tauto

-- Balanced proof
example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPiffQ hQiffR
  cases' hPiffQ with hPQ hQP
  cases' hQiffR with hQR hRQ
  exact ⟨fun hP => hQR (hPQ hP), fun hR => hQP (hRQ hR)⟩


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
