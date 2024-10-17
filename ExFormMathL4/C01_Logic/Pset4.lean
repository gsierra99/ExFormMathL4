import Mathlib.Tactic

variable (P Q R : Prop)

/-- Example 1: P ∧ Q → P -/

-- Detailed proof
example : P ∧ Q → P := by
  intro hPyQ
  cases' hPyQ with hP hQ
  exact hP

-- Automatic proof
example : P ∧ Q → P := by
  tauto

-- Balanced proof
example : P ∧ Q → P := by
  intro hPyQ
  exact hPyQ.left


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
