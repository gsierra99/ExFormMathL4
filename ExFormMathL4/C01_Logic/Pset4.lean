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

-- Comentario de JA: La 11ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 12
example : P ∧ Q → P :=
  fun ⟨hP, _⟩ => hP

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    P ∧ Q → Q
-- ---------------------------------------------------------------------

-- Proof 1
example : P ∧ Q → Q := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ Q
  cases' hPQ with hP hQ
  -- hP : P
  -- hQ : Q
  exact hQ

-- Proof 2
example : P ∧ Q → Q := by
  tauto

-- Proof 3
example : P ∧ Q → Q := by
  intro hPQ
  exact hPQ.right

-- Comentario de JA: En la 1ª demostración se puede usar rcases en lugar
-- de cases' como se muestra a continuación.

-- Proof 4
example : P ∧ Q → Q := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  rcases hPQ with ⟨_hP, hQ⟩
  -- _hP : P
  -- hQ : Q
  -- ⊢ P
  exact hQ

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : P ∧ Q → Q := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  rcases hPQ with ⟨-, hQ⟩
  -- hQ : Q
  exact hQ

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : P ∧ Q → Q := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  have hQ : Q := And.right hPQ
  exact hQ

-- Comentario de JA: La 6ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 7
example : P ∧ Q → Q := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  exact And.right hPQ

-- Comentario de JA: La 7ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 8
example : P ∧ Q → Q :=
  And.right

-- Comentario de JA: La 7ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 9
example : P ∧ Q → Q := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ P
  exact hPQ.2

-- Comentario de JA: Se puede usar rintro como se muestra a
-- continuación.

-- Proof 10
example : P ∧ Q → Q := by
  rintro ⟨_hP, hQ⟩
  -- _hP : P
  -- hQ : Q
  -- ⊢ Q
  exact hQ

-- Comentario de JA: La 10ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 11
example : P ∧ Q → Q := by
  rintro ⟨-, hQ⟩
  -- hQ : Q
  -- ⊢ Q
  exact hQ

-- Comentario de JA: La 11ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 12
example : P ∧ Q → Q :=
  fun ⟨_, hQ⟩ => hQ

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    (P → (Q → R)) → (P ∧ Q → R)
-- ---------------------------------------------------------------------

-- Proof 1
example : (P → (Q → R)) → (P ∧ Q → R) := by
  intro hPQR hPQ
  -- hPQR : P → Q → R
  -- hPQ : P ∧ Q
  -- ⊢ R
  cases' hPQ with hP hQ
  -- hP : P
  -- hQ : Q
  apply hPQR at hP
  -- hP : Q → R
  apply hP at hQ
  -- hQ : R
  exact hQ

-- Proof 2
example : (P → Q → R) → P ∧ Q → R := by
  tauto

-- Proof 3
example : (P → Q → R) → P ∧ Q → R := by
  intro hPQR hPQ
  -- hPQR : P → Q → R
  -- hPQ : P ∧ Q
  -- ⊢ R
  exact hPQR hPQ.left hPQ.right

-- Comentario de JA: La 1ª demostración se puede simplificar (evitando
-- el uso de cases' y la modificación de hipotesis) como se muestra a
-- continuación.

-- Proof 4
example : (P → (Q → R)) → (P ∧ Q → R) := by
  intro hPQR hPQ
  -- hPQR : P → Q → R
  -- hPQ : P ∧ Q
  -- ⊢ R
  rcases hPQ with ⟨hP, hQ⟩
  -- hP : P
  -- hQ : Q
  apply hPQR
  . -- ⊢ P
    exact hP
  . -- ⊢ Q
    exact hQ

-- Comentario de JA: La 4ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 5
example : (P → (Q → R)) → (P ∧ Q → R) := by
  intro hPQR hPQ
  -- hPQR : P → Q → R
  -- hPQ : P ∧ Q
  -- ⊢ R
  apply hPQR
  . -- ⊢ P
    exact hPQ.1
  . -- ⊢ Q
    exact hPQ.2

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : (P → (Q → R)) → (P ∧ Q → R) :=
  fun hPQR hPQ => hPQR hPQ.1 hPQ.2

-- Comentario de JA: Se puede demostrar con rintro como se muestra a
-- continuación.

-- Proof 7
example : (P → (Q → R)) → (P ∧ Q → R) := by
  rintro hPQR ⟨hP, hQ⟩
  -- hPQR : P → Q → R
  -- hP : P
  -- hQ : Q
  -- ⊢ R
  apply hPQR
  . -- ⊢ P
    exact hP
  . -- ⊢ Q
    exact hQ

-- Comentario de JA: La 7ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 8
example : (P → (Q → R)) → (P ∧ Q → R) :=
  fun hPQR ⟨hP, hQ⟩ => hPQR hP hQ

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    P → (Q → P ∧ Q)
-- ---------------------------------------------------------------------

-- Proof 1
example : P → (Q → P ∧ Q) := by
  intro hP hQ
  -- hP : P
  -- hQ : Q
  -- ⊢ P ∧ Q
  constructor
  . -- ⊢ P
    exact hP
  . -- ⊢ Q
    exact hQ

-- Proof 2
example : P → Q → P ∧ Q := by
  tauto

-- Proof 3
example : P → Q → P ∧ Q := by
  intro hP hQ
  -- hP : P
  -- hQ : Q
  -- ⊢ P ∧ Q
  exact ⟨hP, hQ⟩

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P → Q → P ∧ Q :=
  fun hP hQ => ⟨hP, hQ⟩

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    P ∧ Q → Q ∧ P
-- ---------------------------------------------------------------------

-- Proof 1
example : P ∧ Q → Q ∧ P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ Q ∧ P
  cases' hPQ with hP hQ
  -- hP : P
  -- hQ : Q
  -- ⊢ Q ∧ P
  constructor
  . -- ⊢ Q
    exact hQ
  . -- ⊢ P
    exact hP

-- Proof 2
example : P ∧ Q → Q ∧ P := by
  tauto

-- Proof 3
example : P ∧ Q → Q ∧ P := by
  intro hPQ
  -- hPQ : P ∧ Q
  -- ⊢ Q ∧ P
  exact ⟨hPQ.right, hPQ.left⟩

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P ∧ Q → Q ∧ P :=
  fun hPQ => ⟨hPQ.2, hPQ.1⟩

-- Comentario de JA: Se puede sdemostrar con rintro como se muestra a
-- continuación.

-- Proof 5
example : P ∧ Q → Q ∧ P := by
  rintro ⟨hP, hQ⟩
  -- hP : P
  -- hQ : Q
  -- ⊢ Q ∧ P
  exact ⟨hQ, hP⟩

-- Comentario de JA: La 5ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 6
example : P ∧ Q → Q ∧ P :=
  fun ⟨hP, hQ⟩ => ⟨hQ, hP⟩

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    P → P ∧ True
-- ---------------------------------------------------------------------

-- Proof 1
example : P → P ∧ True := by
  intro hP
  -- hP : P
  -- ⊢ P ∧ True
  constructor
  . -- ⊢ P
    exact hP
  . -- ⊢ True
    trivial

-- Proof 2
example : P → P ∧ True := by
  tauto

-- Proof 3
example : P → P ∧ True := by
  intro hP
  -- hP : P
  -- ⊢ P ∧ True
  exact ⟨hP, trivial⟩

-- Comentario de JA: La 3ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 4
example : P → P ∧ True :=
  fun hP => ⟨hP, trivial⟩

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
  intro hPQ hQyR
  cases' hPQ with hP hQ
  cases' hQyR with hQ hR
  constructor
  exact hP
  exact hR

-- Automatic proof
example : P ∧ Q → Q ∧ R → P ∧ R := by
  tauto

-- Balanced proof
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hPQ hQyR
  exact ⟨hPQ.left, hQyR.right⟩


/-- Example 9: (P ∧ Q → R) → P → Q → R -/

-- Detailed proof
example : (P ∧ Q → R) → P → Q → R := by
  intro hPQR hP hQ
  have hPQ : P ∧ Q := ⟨hP, hQ⟩
  apply hPQR at hPQ
  exact hPQ

-- Automatic proof
example : (P ∧ Q → R) → P → Q → R := by
  tauto

-- Balanced proof
example : (P ∧ Q → R) → P → Q → R := by
  intro hPQR hP hQ
  exact hPQR ⟨hP, hQ⟩
