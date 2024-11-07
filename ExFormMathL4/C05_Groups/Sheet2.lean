-- C05_Groups/Pset2.lean
-- Problem set 2
-- Gabriel Sierra Gallego.
-- Seville, November 05, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study basiuc results about weak groups
--
-- It is based on [Section05Groups/Sheet2.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

namespace Section5sheet2


class WeakGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

namespace WeakGroup


variable {G : Type} [WeakGroup G] (a b c : G)


-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    a * b = a * c ⊢ b = c
-- ---------------------------------------------------------------------

-- Proof 1
theorem mul_left_cancel (h : a * b = a * c) : b = c := by
  have h' : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by rw [h]
  rw [← mul_assoc, ← mul_assoc, inv_mul_self, one_mul, one_mul] at h'
  exact h'

-- Proof 2
example (h : a * b = a * c) : b = c := by
  calc
    b = 1 * b := by rw [one_mul]
    _ = a⁻¹ * a * b := by rw [inv_mul_self]
    _ = a⁻¹ * (a * b) := by rw [mul_assoc]
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = a⁻¹ * a * c := by rw [mul_assoc]
    _ = 1 * c := by rw [inv_mul_self]
    _ = c := by rw [one_mul]


-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    b = a⁻¹ * c ⊢ a * b = c
-- ---------------------------------------------------------------------

-- Proof 1
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by
  apply mul_left_cancel a⁻¹
  rwa [← mul_assoc, inv_mul_self, one_mul]


-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    a * 1 = a
-- ---------------------------------------------------------------------

-- Proof 1
theorem mul_one (a : G) : a * 1 = a := by
  apply mul_eq_of_eq_inv_mul
  rw [inv_mul_self]


-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    a * a⁻¹ = 1
-- ---------------------------------------------------------------------

-- Proof 1
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  apply mul_eq_of_eq_inv_mul
  rw [mul_one]

-- ---------------------------------------------------------------------

end WeakGroup



class BadGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

-- No entiendo muy bien lo que sigue, apenas he trabajado con instancias.

instance : One Bool :=
  ⟨Bool.true⟩

instance : Mul Bool :=
  ⟨fun x _y ↦ x⟩

instance : Inv Bool :=
  ⟨fun _x ↦ 1⟩

instance : BadGroup Bool where
  mul_assoc := by decide
  mul_one := by decide
  inv_mul_self := by decide

example : ¬∀ a : Bool, 1 * a = a := by decide
