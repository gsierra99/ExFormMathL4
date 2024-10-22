-- C01_Logic/Pset4.lean
-- Problem set 4: The conjunction.
-- Gabriel Sierra Gallego.
-- Seville, October 22, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study how to work with the conjunction in Lean4.
--
-- It is based on [Section01logic/Sheet4.lean](https://tinyurl.com/29cyxpjz)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

variable (P Q R : Prop)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    P ∧ Q → P
-- ---------------------------------------------------------------------

-- Proof 1
example : P ∧ Q → P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  cases' hPQ with hP hQ
  -- hP : P
  -- hQ : Q
  -- ⊢ P
  exact hP

-- Proof 2
example : P ∧ Q → P := by
  tauto

-- Proof 3
example : P ∧ Q → P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  exact hPQ.left

-- Comentario de JA: En la 1ª demostración se puede usar rcases en lugar
-- de cases' como se muestra a continuación.

-- Proof 4
example : P ∧ Q → P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  rcases hPQ with ⟨hP, _hQ⟩
  -- hP : P
  -- _hQ : Q
  -- ⊢ P
  exact hP

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P ∧ Q → P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  rcases hPQ with ⟨hP, -⟩
  -- hP : P
  -- ⊢ P
  exact hP

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : P ∧ Q → P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  have hP : P := And.left hPQ
  exact hP

-- Comentario de JA: La 6ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : P ∧ Q → P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  exact And.left hPQ

-- Comentario de JA: La 7ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 8
example : P ∧ Q → P :=
  And.left

-- Comentario de JA: La 7ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 9
example : P ∧ Q → P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  exact hPQ.1

-- Comentario de JA: Se puede usar rintro como se muestra a
-- continuación.

-- Proof 10
example : P ∧ Q → P := by
  rintro ⟨hP, _hQ⟩
  -- hP : P
  -- _hQ : Q
  -- ⊢ P
  exact hP

-- Comentario de JA: La 10ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 11
example : P ∧ Q → P := by
  rintro ⟨hP, -⟩
  -- hP : P
  -- ⊢ P
  exact hP


/-- Example 2: P ∧ Q → Q -/

-- Detailed proof
example : P ∧ Q → Q := by
  intro hPyQ
  cases' hPyQ with hP hQ
  exact hQ

-- Automatic proof
example : P ∧ Q → Q := by
  tauto

-- Balanced proof
example : P ∧ Q → Q := by
  intro hPyQ
  exact hPyQ.right


/-- Example 3: (P → Q → R) → P ∧ Q → R -/
-- Detailed proof
example : (P → Q → R) → P ∧ Q → R := by
  intro hPQR hPyQ
  cases' hPyQ with hP hQ
  apply hPQR at hP
  apply hP at hQ
  exact hQ

-- Automatic proof
example : (P → Q → R) → P ∧ Q → R := by
  tauto

-- Balanced proof
example : (P → Q → R) → P ∧ Q → R := by
  intro hPQR hPyQ
  exact hPQR hPyQ.left hPyQ.right


/-- Example 4: P → Q → P ∧ Q -/
-- Detailed proof
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  exact hP
  exact hQ

-- Automatic proof
example : P → Q → P ∧ Q := by
  tauto

-- Balanced proof
example : P → Q → P ∧ Q := by
  intro hP hQ
  exact ⟨hP, hQ⟩



/-- Example 5: P ∧ Q → Q ∧ P -/
-- Detailed proof
example : P ∧ Q → Q ∧ P := by
  intro hPyQ
  cases' hPyQ with hP hQ
  constructor
  exact hQ
  exact hP

-- Automatic proof
example : P ∧ Q → Q ∧ P := by
  tauto

-- Balanced proof
example : P ∧ Q → Q ∧ P := by
  intro hPyQ
  exact ⟨hPyQ.right, hPyQ.left⟩


/-- Example 6: P → P ∧ True -/
-- Detailed proof
example : P → P ∧ True := by
  intro hP
  constructor
  exact hP
  trivial

-- Automatic proof
example : P → P ∧ True := by
  tauto

-- Balanced proof
example : P → P ∧ True := by
  intro hP
  exact ⟨hP, trivial⟩


/-- Example 7: False → P ∧ False -/

-- Detailed proof
example : False → P ∧ False := by
  intro hF
  constructor
  exfalso
  exact hF
  exact hF

-- Automatic proof
example : False → P ∧ False := by
  tauto

-- Balanced proof
example : False → P ∧ False := by
  intro hF
  contradiction


/-- Example 8: P ∧ Q → Q ∧ R → P ∧ R -/

-- Detailed proof
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hPyQ hQyR
  cases' hPyQ with hP hQ
  cases' hQyR with hQ hR
  constructor
  exact hP
  exact hR

-- Automatic proof
example : P ∧ Q → Q ∧ R → P ∧ R := by
  tauto

-- Balanced proof
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hPyQ hQyR
  exact ⟨hPyQ.left, hQyR.right⟩


/-- Example 9: (P ∧ Q → R) → P → Q → R -/

-- Detailed proof
example : (P ∧ Q → R) → P → Q → R := by
  intro hPyQR hP hQ
  have hPyQ : P ∧ Q := ⟨hP, hQ⟩
  apply hPyQR at hPyQ
  exact hPyQ

-- Automatic proof
example : (P ∧ Q → R) → P → Q → R := by
  tauto

-- Balanced proof
example : (P ∧ Q → R) → P → Q → R := by
  intro hPyQR hP hQ
  exact hPyQR ⟨hP, hQ⟩
