-- C05_Groups/Pset1.lean
-- Problem set 1
-- Gabriel Sierra Gallego.
-- Seville, November 05, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study basic results about groups
--
-- It is based on [Section05Groups/Sheet1.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic


variable (G : Type) [Group G]

example (g : G) : g⁻¹ * g = 1 :=
  inv_mul_cancel g

example (a b c : G) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

example (a : G) : a * 1 = a := by
  exact MulOneClass.mul_one a

example (a : G) : 1 * a = a := by
  exact one_mul a

example (a : G) : a * a⁻¹ = 1 := by
  exact mul_inv_cancel a


variable (a b c : G)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    a⁻¹ * (a * b) = b
-- ---------------------------------------------------------------------

-- Proof 1
example : a⁻¹ * (a * b) = b := by
  rw [ ← mul_assoc]
  rw [inv_mul_cancel]
  rw [one_mul]

-- Proof 2
example : a⁻¹ * (a * b) = b := by
  exact inv_mul_cancel_left a b

-- Proof 3
example : a⁻¹ * (a * b) = b := by
  rw [ ← mul_assoc, inv_mul_cancel, one_mul]

-- Proof 4
example : a⁻¹ * (a * b) = b := by
  group


-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    a * (a⁻¹ * b) = b
-- ---------------------------------------------------------------------

-- Proof 1
example : a * (a⁻¹ * b) = b := by
  rw [ ← mul_assoc]
  rw [mul_inv_cancel]
  rw [one_mul]

-- Proof 2
example : a * (a⁻¹ * b) = b := by
  exact mul_inv_cancel_left a b

-- Proof 3
example : a * (a⁻¹ * b) = b := by
  rw [ ← mul_assoc, mul_inv_cancel, one_mul]

-- Proof 4
example : a * (a⁻¹ * b) = b := by
  group

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    b = c given b * a = 1 and a * c = 1
-- ---------------------------------------------------------------------

-- Proof 1
example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  have h3 : b = a⁻¹ := by
    exact eq_inv_of_mul_eq_one_left h1
  have h4 : c = a⁻¹ := by
    exact Eq.symm (DivisionMonoid.inv_eq_of_mul a c h2)
  rw [h3, h4]

-- Proof 2
example {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : b = c := by
  have h3 : b * a = a * c := by rw [h1, h2]
  have h4 : a⁻¹ * b * a = a⁻¹ * a * c := by
    calc
      a⁻¹ * b * a = a⁻¹ * (b * a) := by rw [mul_assoc]
      _ = a⁻¹ * (a * c) := by rw [h3]
      _ = a⁻¹ * a * c := by rw [mul_assoc]
  rw [mul_assoc, h1, mul_one, inv_mul_cancel, one_mul] at h4
  have h6 : b * a * a⁻¹ = a * c * a⁻¹ := by rw [h3]
  rw [mul_assoc, mul_inv_cancel, mul_one, h2, one_mul ] at h6
  rw [h6, h4]






-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    a * b = 1 ↔ a⁻¹ = b
-- ---------------------------------------------------------------------

-- Proof 1
example : a * b = 1 ↔ a⁻¹ = b := by
  constructor
  intro h1
  have h1' : a⁻¹ * (a * b) = a⁻¹ * 1 := by rw [h1]
  rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h1'
  exact Eq.symm h1'
  intro h2
  rw [← h2]
  rw [mul_inv_cancel]

-- Proof 2
example : a * b = 1 ↔ a⁻¹ = b := by
  constructor
  intro h1
  exact DivisionMonoid.inv_eq_of_mul a b h1
  intro h2
  exact mul_eq_one_iff_inv_eq.mpr h2


-- ---------------------------------------------------------------------
-- Exercise 5. Prove that
--    (1 : G)⁻¹ = 1
-- ---------------------------------------------------------------------

-- Proof 1
example : (1 : G)⁻¹ = 1 := by
  have h2 : (1 : G)⁻¹ * (1 * 1) = 1⁻¹ * 1 := by
    rw [@Monoid.mul_one]
  rw [← mul_assoc] at h2
  nth_rw 1 [mul_one] at h2
  nth_rw 1 [mul_one] at h2
  rw [inv_mul_cancel] at h2
  exact h2

-- Proof 2
example : (1 : G)⁻¹ = 1 := by
  exact inv_one

-- Proof 3
example : (1 : G)⁻¹ = 1 := by
  group

-- Proof 4
example : (1 : G)⁻¹ = 1 := by
  have he : (1 : G) = 1 := by exact rfl
  have he' : (1 : G)⁻¹ * 1 * 1 = 1⁻¹ * 1 * 1 := by rw [he]
  nth_rw 1 [mul_assoc,] at he'
  nth_rw 1 [one_mul] at he'
  nth_rw 1 [mul_one] at he'
  rw [inv_mul_cancel] at he'
  rw [one_mul] at he'
  exact he'

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that
--    a⁻¹⁻¹ = a
-- ---------------------------------------------------------------------

-- Proof 1
example : a⁻¹⁻¹ = a := by
  exact DivisionMonoid.inv_inv a

-- Proof 2
example : a⁻¹⁻¹ = a := by
  group

-- Proof 3
example : a⁻¹⁻¹ = a := by
  rw [← mul_eq_one_iff_inv_eq, inv_mul_cancel]


-- ---------------------------------------------------------------------
-- Exercise 7. Prove that
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ---------------------------------------------------------------------

-- Proof 1
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  suffices (a * b) * (b⁻¹ * a⁻¹) = 1 by
    exact DivisionMonoid.mul_inv_rev a b
  calc
    a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) := by rw [mul_assoc]
    _ = a * ((b * b⁻¹) * a⁻¹) := by rw [mul_assoc]
    _ = a * (1 * a⁻¹) := by rw [mul_inv_cancel]
    _ = a * a⁻¹ := by rw [one_mul]
    _ = 1 := by rw [mul_inv_cancel]

-- Proof 2
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group

-- Proof 3
example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← mul_eq_one_iff_inv_eq, ← mul_assoc, mul_assoc a, mul_inv_cancel, mul_one, mul_inv_cancel]



-- ---------------------------------------------------------------------
-- Exercise 8. Prove that
--    if g^2=1 for all g in G, then G is abelian
-- ---------------------------------------------------------------------

-- Proof 1
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  intro a b
  have h' : ∀ g : G, g = g⁻¹ := by
    exact fun g => eq_inv_of_mul_eq_one_left (h g)
  calc
    a * b = a⁻¹ * b⁻¹ := sorry -- by rw [h' (a * b), ...]  ? -- aplicación de que todo elemento es su propio inverso
    _ = (b * a)⁻¹ := by group -- aplicación del resultado del ej anterior
    _ = b * a := by sorry -- aplicación de que todo elemento es su propio inverso

-- Proof 2
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g :=
  by
  have useful : ∀ g : G, g = g⁻¹ := by
    intro g
    rw [← eq_comm, ← mul_eq_one_iff_inv_eq]
    exact h g
  intro g h
  rw [useful (g * h), mul_inv_rev, ← useful g, ← useful h]

-- Proof 3
example (h : ∀ g : G, g * g = 1) : ∀ g h : G, g * h = h * g := by
  sorry
