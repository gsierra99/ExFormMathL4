-- C04_Sets/Pset3.lean
-- Problem set 3
-- Gabriel Sierra Gallego.
-- Seville, November 03, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study results about sets and their complements.
--
-- It is based on [Section04functions/Sheet3.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

open Set

variable (X : Type)
variable (A B C D E : Set X)
variable (x y z : X)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    x ∉ A → x ∈ A → False
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : x ∉ A → x ∈ A → False := by
  intro hxnA hxA
  apply hxnA
  exact hxA


-- Proof 2 (automatic)
example : x ∉ A → x ∈ A → False := by
  exact fun a a_1 => a a_1

-- Proof 3 (equilibrated)
example : x ∉ A → x ∈ A → False := by
  simp


-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    x ∈ A → x ∉ A → False
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : x ∈ A → x ∉ A → False := by
    intro hxA hxnA
    apply hxnA
    exact hxA

-- Proof 2 (automatic)
example : x ∈ A → x ∉ A → False := by
    exact fun a a_1 => a_1 a

-- Proof 3 (equilibrated)
 example : x ∈ A → x ∉ A → False := by
    simp


  -- ---------------------------------------------------------------------
  -- Exercise 3. Prove that
  --    A ⊆ B → x ∉ B → x ∉ A
  -- ---------------------------------------------------------------------

  -- Proof 1 (detailed)
example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAinB hxninB
  rw [subset_def] at hAinB
  by_contra hxinA
  apply hAinB at hxinA
  apply hxninB
  exact hxinA

  -- Proof 2 (automatic)
example : A ⊆ B → x ∉ B → x ∉ A := by
  exact fun a a_1 a_2 => a_1 (a a_2)

  -- Proof 3 (equilibrated)
example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAsB hxneB
  rw [subset_def] at hAsB
  exact fun a => hxneB (hAsB x a)


  -- ---------------------------------------------------------------------
  -- Exercise 4. Prove that
  --    x ∉ (∅ : Set X)
  -- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : x ∉ (∅ : Set X) := by
  by_contra hxinv
  cases hxinv

-- Proof 2 (automatic)
example : x ∉ (∅ : Set X) := by
  exact fun a => a

-- Proof 3 (equilibrated)
example : x ∉ (∅ : Set X) := by
  simp

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    x ∈ Aᶜ → x ∉ A
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : x ∈ Aᶜ → x ∉ A := by
  intro hxinAc
  by_contra hxninAc
  exact hxinAc hxninAc

-- Proof 2 (automatic)
example : x ∈ Aᶜ → x ∉ A := by
  exact fun a => a

-- Proof 3 (equilibrated)
example : x ∈ Aᶜ → x ∉ A := by
  simp

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  intro hAisU
  by_contra hExinAc
  cases' hExinAc with x hxinAyC
  specialize hAisU x
  exact hxinAyC hAisU
  intro hnExinAc
  intro x
  simp at hnExinAc
  specialize hnExinAc x
  exact hnExinAc

-- Proof 2 (automatic)
example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  intro hAisU
  exact not_exists.mpr fun x a => a (hAisU x)
  intro hnExinAc
  intro x
  simp at hnExinAc
  exact hnExinAc x

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ
-- ---------------------------------------------------------------------

-- Proof 1 (detailed)
example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  intro hExinA
  simp
  obtain ⟨x, hxinA⟩ := hExinA
  exact Exists.intro x hxinA


-- Proof 2 (automatic)
example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  exact Iff.symm Classical.not_forall_not

-- Proof 3 (equilibrated)
example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  intro hExinA
  simp
  exact hExinA
