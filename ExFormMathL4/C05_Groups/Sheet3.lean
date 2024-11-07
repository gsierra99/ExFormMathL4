-- C05_Groups/Pset3.lean
-- Problem set 3
-- Gabriel Sierra Gallego.
-- Seville, November 05, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we study results about group homomorphisms.
--
-- It is based on [Section05Groups/Sheet3.lean](https://tinyurl.com/2xlkt9kh)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic


section Subgroups

variable (G : Type) [Group G]
variable (H : Subgroup G)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that
--    a ∈ H, b ∈ H ⊢ a * b ∈ H
-- ---------------------------------------------------------------------

-- Proof 1
example (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  exact H.mul_mem ha hb

-- Proof 2
example (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  sorry

-- se me ocurre una demostración por reducción al absurdo, empleando que un grupo es cerrado
-- para su operación interna, pero no sé cómo ponerlo en pie.


-- ---------------------------------------------------------------------
-- Exercise 2. Prove that
--    a ∈ H, b ∈ H, c ∈ H ⊢ a * b⁻¹ * 1 * (a * c) ∈ H
-- ---------------------------------------------------------------------

-- Proof 1
example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) : a * b⁻¹ * 1 * (a * c) ∈ H := by
  have hb' : b⁻¹ ∈ H := by exact H.inv_mem hb
  have h1 : (1 : G) ∈ H := by exact H.one_mem
  have h2 : a * c ∈ H := by exact H.mul_mem ha hc
  have h3 : a * b⁻¹ ∈ H := by exact H.mul_mem ha hb'
  have h4 : a * b⁻¹ * 1 ∈ H := by exact H.mul_mem h3 h1
  exact H.mul_mem h4 h2

-- Proof 2
example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * b⁻¹ * 1 * (a * c) ∈ H := by
  refine H.mul_mem (H.mul_mem (H.mul_mem ha ?_) H.one_mem) (H.mul_mem ha hc)
  exact H.inv_mem hb


-- ---------------------------------------------------------------------

example (H K : Subgroup G) : Subgroup G := H ⊓ K

example (H K : Subgroup G) (a : G) : a ∈ H ⊓ K ↔ a ∈ H ∧ a ∈ K := by
  rfl

-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that
--    a ∈ H ∨ a ∈ K → a ∈ H ⊔ K
-- ---------------------------------------------------------------------

-- Proof 1
example (H K : Subgroup G) (a : G) : a ∈ H ∨ a ∈ K → a ∈ H ⊔ K := by
  intro h
  obtain h | h : a ∈ H ∨ a ∈ K := h
  exact Subgroup.mem_sup_left h
  exact Subgroup.mem_sup_right h


-- Proof 2
example (H K : Subgroup G) (a : G) : a ∈ H ∨ a ∈ K → a ∈ H ⊔ K := by
  rintro (hH | hK)
  · exact Subgroup.mem_sup_left hH
  · exact Subgroup.mem_sup_right hK


-- ---------------------------------------------------------------------

end Subgroups


section Homomorphisms


variable (G H : Type) [Group G] [Group H]
variable (φ : G →* H)

example (a b : G) : φ (a * b) = φ a * φ b :=
  φ.map_mul a b



-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1
-- ---------------------------------------------------------------------

-- Proof 1
example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  have hb' : φ b⁻¹ = (φ b)⁻¹ := by exact φ.map_inv b
  have h1 : φ (1 : G) = 1 := by exact φ.map_one
  rw [φ.map_mul, φ.map_mul, hb', h1]

-- Proof 2
example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  rw [φ.map_mul, φ.map_mul, φ.map_one, φ.map_inv]


-- ---------------------------------------------------------------------
-- Exercise 4. Prove that
--    ∀ g : G, φ g = ψ g ⊢ φ = ψ
-- ---------------------------------------------------------------------

-- Proof 1
example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  ext x
  exact h x

-- Proof 2
example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  ext a
  apply h

end Homomorphisms
