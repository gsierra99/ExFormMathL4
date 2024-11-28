-- C02_Reals/Pset6.lean
-- Problem set 6: Limits of sequences (3)
-- Gabriel Sierra Gallego.
-- Seville, November 11, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we prove some theorems about the limit of
-- a sequence.
--
-- It is based on [Section02reals/Sheet6.lean](https://tinyurl.com/2xly8hhc)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic
import ExFormMathL4.C02_Reals.Pset5

namespace Section2sheet6

open Section2sheet3 Section2sheet5

variable {a : ℕ → ℝ}
variable {t : ℝ}
variable (c : ℝ)

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that if `a(n)` tends to `t` then `37 * a(n)` tends
-- to `37 * t`.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Let ε > 0. We need to prove that there exists an B ∈ ℕ such that
--    (∀ n ∈ ℕ)[B ≤ n → |37u(n) - 37a| < ε]                             (1)
-- Since u(n) tends to a, there exists an B ∈ ℕ such that
--    (∀ n ∈ ℕ)[B ≤ n → |u(n) - a| < ε/37]                              (2)
-- Let B ∈ ℕ that satisfies (2), let's see that the same B satisfies
-- (1). For this, let n ∈ ℕ such that B ≤ n. Then,
--    |37u(n) - 37a| = |37(u(n) - a)|
--                   = |37||u(n) - a|
--                   = 37|u(n) - a|
--                   < 37(ε / 37)        [by (2)]
--                   = ε

-- Proof 1
-- =======

example
  (h : TendsTo a t)
  : TendsTo (fun n ↦ 37 * a n) (37 * t) :=
by
  rw [TendsTo] at *
  -- h : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  -- ⊢ ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |37 * a n - 37 * t| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |37 * a n - 37 * t| < ε
  have hε' : 0 < ε / 37 := by linarith
  specialize h (ε / 37) hε'
  -- h : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε / 37
  cases' h with B hB
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / 37
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |37 * a n - 37 * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |37 * a n - 37 * t| < ε
  specialize hB n hn
  -- hB : |a n - t| < ε / 37
  calc |37 * a n - 37 * t|
     = |37 * (a n - t)|    := by rw [← mul_sub]
   _ = |37| * |a n - t|    := by rw [abs_mul]
   _ = 37 * |a n - t|      := by rw [abs_of_nonneg]; linarith
   _ < 37 * (ε / 37)       := by linarith
   _ = ε                   := by linarith

-- Proof 2
-- =======

example
  (h : TendsTo a t)
  : TendsTo (fun n ↦ 37 * a n) (37 * t) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => 37 * a n) n - 37 * t| < ε
  obtain ⟨B, hB⟩ := h (ε / 37) (by linarith)
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / 37
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |(fun n => 37 * a n) n - 37 * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |(fun n => 37 * a n) n - 37 * t| < ε
  specialize hB n hn
  -- hB : |a n - t| < ε / 37
  simp
  -- ⊢ |37 * a n - 37 * t| < ε
  rw [← mul_sub, abs_mul, abs_of_nonneg] <;> linarith

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 3
-- =======

example
  (h : TendsTo a t)
  : TendsTo (fun n ↦ 37 * a n) (37 * t) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => 37 * a n) n - 37 * t| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |37 * a n - 37 * t| < ε
  have hε' : 0 < ε / 37 := by linarith
  replace h : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε / 37 := h (ε / 37) hε'
  obtain ⟨B, hB⟩ := h
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / 37
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |37 * a n - 37 * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |37 * a n - 37 * t| < ε
  replace hB : |a n - t| < ε / 37 := hB n hn
  calc |37 * a n - 37 * t|
     = |37 * (a n - t)|    := by rw [← mul_sub]
   _ = |37| * |a n - t|    := by rw [abs_mul]
   _ = 37 * |a n - t|      := by rw [abs_of_nonneg]; linarith
   _ < 37 * (ε / 37)       := by linarith
   _ = ε                   := by linarith

-- Comentario de JA: La 2ª demostración se puede modificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example
  (h : TendsTo a t)
  : TendsTo (fun n ↦ 37 * a n) (37 * t) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => 37 * a n) n - 37 * t| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |37 * a n - 37 * t| < ε
  obtain ⟨B, hB⟩ := h (ε / 37) (by linarith)
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / 37
  use B
  -- ⊢ ⊢ ∀ (n : ℕ), B ≤ n → |37 * a n - 37 * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |37 * a n - 37 * t| < ε
  replace hB : |a n - t| < ε / 37 := hB n hn
  rw [← mul_sub]
  -- ⊢ |37 * (a n - t)| < ε
  rw [abs_mul]
  -- ⊢ |37| * |a n - t| < ε
  rw [abs_of_nonneg]
  . -- ⊢ 37 * |a n - t| < ε
    linarith
  . -- ⊢ 0 ≤ 37
    linarith

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that if `a(n)` tends to `t` and `c` is a positive
-- constant then `c * a(n)` tends to `c * t`.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε > 0. Tenemos que demostrar que existe un B ∈ ℕ tal que
--    (∀n ∈ ℕ)[B ≤ n → |c·a(n) - c·t| < ε]                           (1)
-- Puesto que a(n) tends to c, existe un B ∈ ℕ tal que
--    (∀n ∈ ℕ)[B ≤ n → |a(n) - t| < ε/c]                             (2)
-- Sea B ∈ ℕ tal que se verifica (2). Veamos que entonces también se
-- verifica (1). Para ello, sea n ∈ ℕ tal que
--    B ≤ n                                                          (3)
-- Entonces,
--    |c·a(n) - c·t| = |c(a(n) - t)|
--                   = |c|·|a(n) - t|
--                   = c·|a(n) - t|     [porque c > 0]
--                   < c·(ε/c)          [por (2) y (3)
--                   = ε·(c/c)
--                   = ε·1
--                   = ε

-- Proof 1
-- =======

example
  (h : TendsTo a t)
  (hc : 0 < c)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  rw [TendsTo] at *
  -- h : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  -- ⊢ ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  have heps : 0 < ε / c := by exact div_pos hε hc
  obtain ⟨B, hB⟩ := h (ε / c) heps
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |c * a n - c * t| < ε
  specialize hB n hn
  -- hB : |a n - t| < ε / c
  have hc' : c ≠ 0 := by linarith
  calc |c * a n - c * t|
     = |c * (a n - t)|   := by rw [← mul_sub]
   _ = |c| * |a n - t|   := by rw [abs_mul]
   _ = c * |a n - t|     := by rw [abs_of_nonneg]; linarith
   _ < c * (ε / c)       := by exact (mul_lt_mul_left hc).mpr hB
   _ = (c * ε) / c       := by exact Eq.symm (mul_div_assoc c ε c)
   _ = (ε * c) / c       := by rw [mul_comm]
   _ = ε * (c / c)       := by rw [mul_div_assoc ε c c]
   _ = ε * 1             := by rw [div_self hc']
   _ = ε                 := by linarith

-- Proof 2
-- =======

example
  (h : TendsTo a t)
  (hc : 0 < c)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  rw [TendsTo] at *
  -- h : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  -- ⊢ ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  have heps : 0 < (ε / c) := by exact div_pos hε hc
  obtain ⟨B, hB⟩ := h (ε / c) heps
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |c * a n - c * t| < ε
  specialize hB n hn
  -- hB : |a n - t| < ε / c
  rw [← mul_sub, abs_mul, abs_of_nonneg]
  . -- ⊢ c * |a n - t| < ε
    rw[← lt_div_iff₀']
    -- ⊢ |a n - t| < ε / c
    linarith
    -- ⊢ 0 < c
    exact hc
  . -- ⊢ 0 ≤ c
    linarith

-- Comentario de JA: La 1ª demostración se puede modificar como se
-- muestra a continuación.

-- Proof 3
-- =======

example
  (h : TendsTo a t)
  (hc : 0 < c)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => c * a n) n - c * t| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  have heps : 0 < ε / c := div_pos hε hc
  obtain ⟨B, hB⟩ := h (ε / c) heps
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |c * a n - c * t| < ε
  replace hB : |a n - t| < ε / c := hB n hn
  have hc' : c ≠ 0 := (ne_of_lt hc).symm
  calc |c * a n - c * t|
     = |c * (a n - t)|   := congr_arg abs (mul_sub_left_distrib c (a n) t).symm
   _ = |c| * |a n - t|   := abs_mul c (a n - t)
   _ = c * |a n - t|     := congrArg (. * |a n - t|) (abs_of_pos hc)
   _ < c * (ε / c)       := (mul_lt_mul_left hc).mpr hB
   _ = (c * ε) / c       := (mul_div_assoc c ε c).symm
   _ = (ε * c) / c       := congrArg (. / c) (mul_comm c ε)
   _ = ε * (c / c)       := mul_div_assoc ε c c
   _ = ε * 1             := congrArg (ε * .) (div_self hc')
   _ = ε                 := mul_one ε

-- Comentario de JA: La 3ª demostración se puede modificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example
  (h : TendsTo a t)
  (hc : 0 < c)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => c * a n) n - c * t| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  have heps : 0 < ε / c := div_pos hε hc
  obtain ⟨B, hB⟩ := h (ε / c) heps
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |c * a n - c * t| < ε
  replace hB : |a n - t| < ε / c := hB n hn
  have hc' : c ≠ 0 := (ne_of_lt hc).symm
  calc |c * a n - c * t|
     = |c * (a n - t)|   := by simp [mul_sub_left_distrib]
   _ = |c| * |a n - t|   := by simp [abs_mul]
   _ = c * |a n - t|     := by simp [abs_of_pos hc]
   _ < c * (ε / c)       := by simp [mul_lt_mul_left hc, hB]
   _ = (c * ε) / c       := by simp [mul_div_assoc]
   _ = ε * 1             := by simp [hc']
   _ = ε                 := by linarith

-- Comentario de JA: La 2ª demostración se puede modificar como se
-- muestra a continuación.

-- Proof 5
-- =======

lemma tendsTo_pos_const_mul
  (h : TendsTo a t)
  (hc : 0 < c)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => c * a n) n - c * t| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  have heps : 0 < (ε / c) := div_pos hε hc
  obtain ⟨B, hB⟩ := h (ε / c) heps
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |c * a n - c * t| < ε
  replace hB : |a n - t| < ε / c := hB n hn
  rw [← mul_sub]
  -- ⊢ |c * (a n - t)| < ε
  rw [abs_mul]
  -- ⊢ |c| * |a n - t| < ε
  rw [abs_of_nonneg]
  . -- ⊢ c * |a n - t| < ε
    rw[← lt_div_iff₀']
    -- ⊢ |a n - t| < ε / c
    exact hB
    -- ⊢ 0 < c
    exact hc
  . -- ⊢ 0 ≤ c
    exact le_of_lt hc

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that if `a(n)` tends to `t` and `c` is a negative
-- constant then `c * a(n)` tends to `c * t`.
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- If c < 0, then -c > 0 and, by tendsTo_pos_const_mul, -c⋅a(n) tends to
-- -c⋅t and, by tendsTo_neg, c⋅a(n) tends to c⋅t.

-- Proof 1
-- =======

example
  (h : TendsTo a t)
  (hc : c < 0)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  rw [TendsTo] at *
  -- h : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  -- ⊢ ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  have hc' : 0 < -c := by linarith
  have heps : 0 < ε / -c := by exact div_pos hε hc'
  obtain ⟨B, hB⟩ := h (ε / -c) heps
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / -c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |c * a n - c * t| < ε
  specialize hB n hn
  -- hB : |a n - t| < ε / -c
  calc |c * a n - c * t|
     = |c * (a n - t)| := by rw [← mul_sub]
   _ = |c| * |a n - t| := by rw [abs_mul]
   _ = -c * |a n - t|  := by rw [abs_of_nonpos]; linarith
   _ < -c * (ε / -c)   := by exact (mul_lt_mul_left hc').mpr hB
   _ = (-c * ε) / -c   := by exact Eq.symm (mul_div_assoc (-c) ε (-c))
   _ = (ε * -c) / -c   := by rw [mul_comm]
   _ = ε * (-c / -c)   := by rw [mul_div_assoc ε (-c) (-c)]
   _ = ε * (c / c)     := by rw [neg_div_neg_eq]
   _ = ε * 1           := by have hc'' : c ≠ 0 := by linarith
                             rw [div_self hc'']
   _ = ε               := by linarith

-- Proof 2
-- =======

example
  (h : TendsTo a t)
  (hc : c < 0)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  have hc' : 0 < -c := neg_pos.mpr hc
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => c * a n) n - c * t| < ε
  obtain ⟨B, hB⟩ := h (ε / -c) (div_pos hε hc')
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / -c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |(fun n => c * a n) n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |(fun n => c * a n) n - c * t| < ε
  specialize hB n hn
  -- hB : |a n - t| < ε / -c
  simp
  -- ⊢ |c * a n - c * t| < ε
  rw [← mul_sub, abs_mul, abs_of_neg hc]
  -- ⊢ -c * |a n - t| < ε
  exact (lt_div_iff₀' hc').mp hB

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 3
-- =======

example
  (h : TendsTo a t)
  (hc : c < 0)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => c * a n) n - c * t| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  have hc' : 0 < -c := Left.neg_pos_iff.mpr hc
  have heps : 0 < ε / -c := div_pos hε hc'
  obtain ⟨B, hB⟩ := h (ε / -c) heps
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / -c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |c * a n - c * t| < ε
  replace hB : |a n - t| < ε / -c := hB n hn
  have hc'' : c ≠ 0 := (ne_of_gt hc).symm
  calc |c * a n - c * t|
     = |c * (a n - t)| := congr_arg abs (mul_sub_left_distrib c (a n) t).symm
   _ = |c| * |a n - t| := abs_mul c (a n - t)
   _ = -c * |a n - t|  := congrArg (. * |a n - t|) (abs_of_neg hc)
   _ < -c * (ε / -c)   := (mul_lt_mul_left hc').mpr hB
   _ = (-c * ε) / -c   := (mul_div_assoc (-c) ε (-c)).symm
   _ = (ε * -c) / -c   := congrArg (. / -c) (mul_comm ε (-c)).symm
   _ = ε * (-c / -c)   := mul_div_assoc ε (-c) (-c)
   _ = ε * (c / c)     := congrArg (ε * .) (neg_div_neg_eq c c)
   _ = ε * 1           := congrArg (ε * .) (div_self hc'')
   _ = ε               := mul_one ε

-- Comentario de JA: La 2ª demostración se puede modificar como se
-- muestra a continuación.

-- Proof 4
-- =======

example
  (h : TendsTo a t)
  (hc : c < 0)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  have hc' : 0 < -c := neg_pos.mpr hc
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => c * a n) n - c * t| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  obtain ⟨B, hB⟩ := h (ε / -c) (div_pos hε hc')
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε / -c
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |c * a n - c * t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |c * a n - c * t| < ε
  replace hB : |a n - t| < ε / -c := hB n hn
  rw [← mul_sub]
  -- ⊢ |c * (a n - t)| < ε
  rw [abs_mul]
  -- ⊢ |c| * |a n - t| < ε
  rw [abs_of_neg hc]
  -- ⊢ -c * |a n - t| < ε
  exact (lt_div_iff₀' hc').mp hB

-- Comentario de JA: Se puede demostrar usando ejercicios anteriores
-- como se muestra a continuación.

-- Proof 5
-- =======

lemma tendsTo_neg_const_mul
  (h : TendsTo a t)
  (hc : c < 0)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  have h1 : 0 < -c := Left.neg_pos_iff.mpr hc
  have h2 : TendsTo (fun n ↦ -c * a n) (-c * t)
    := by exact tendsTo_pos_const_mul (-c) h h1
  have h3 : TendsTo (fun n ↦ -(-c * a n)) (-(-c * t))
    := tendsTo_neg h2
  show TendsTo (fun n ↦ c * a n) (c * t)
  aesop

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that if `a(n)` tends to `t` and `c` is a constant
-- then `c * a(n)` tends to `c * t`.
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- Three cases are considered.
--
-- Case 1: Suppose that c > 0. Then, by the property
-- tendsTo_pos_const_mul, we have the desired result.
--
-- Case 2: Suppose that c = 0. Then, by the property tendsTo_const, we
-- obtain the result.
--
-- Case 3: Suppose that c < 0. Then, by the property
-- tendsTo_neg_const_mul, the result follows.

-- Proof 1
-- =======

example
  (h : TendsTo a t)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  obtain hcpos | hczero | hcneg := lt_trichotomy 0 c
  . -- hcpos : 0 < c
    -- ⊢ TendsTo (fun n => c * a n) (c * t)
    exact tendsTo_pos_const_mul c h hcpos
  . -- hczero : 0 = c
    -- ⊢ TendsTo (fun n => c * a n) (c * t)
    rw [← hczero]
    -- ⊢ TendsTo (fun n => 0 * a n) (0 * t)
    simp
    -- ⊢ TendsTo (fun n => 0) 0
    exact tendsTo_const 0
  . -- hcneg : c < 0
    -- ⊢ TendsTo (fun n => c * a n) (c * t)
    exact tendsTo_neg_const_mul c h hcneg

-- Proof 2
-- =======

theorem tendsTo_const_mul
  (h : TendsTo a t)
  : TendsTo (fun n ↦ c * a n) (c * t) :=
by
  obtain hc | rfl | hc := lt_trichotomy 0 c
  · -- hc : 0 < c
    -- ⊢ TendsTo (fun n => c * a n) (c * t)
    exact tendsTo_pos_const_mul c h hc
  · -- ⊢ TendsTo (fun n => 0 * a n) (0 * t)
    simpa using tendsTo_const 0
  · -- hc : c < 0
    -- ⊢ TendsTo (fun n => c * a n) (c * t)
    exact tendsTo_neg_const_mul c h hc

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that if `a(n)` tends to `t` and `c` is a constant
-- then `a(n) * c` tends to `t * c`.
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- It is an immediate consequence of tendsTo_const_mul.

-- Proof 1
-- =======

example
  (c : ℝ)
  (h : TendsTo a t)
  : TendsTo (fun n ↦ a n * c) (t * c) :=
by
  simp [mul_comm]
  -- ⊢ TendsTo (fun n => c * a n) (c * t)
  rw [mul_comm]
  -- ⊢ TendsTo (fun n => c * a n) (t * c)
  exact tendsTo_const_mul c h

-- Proof 2
-- =======

theorem tendsTo_mul_const
  (c : ℝ)
  (h : TendsTo a t)
  : TendsTo (fun n ↦ a n * c) (t * c) :=
by
  simpa [mul_comm] using tendsTo_const_mul c h

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that if `a(n)` tends to `t`,  then `-a(n)` tends
-- to `-t`.
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example
  (ha : TendsTo a t)
  : TendsTo (fun n ↦ -a n) (-t) :=
by
  have h : TendsTo (fun n ↦ -1 * a n) (-1 * t)
    := tendsTo_const_mul (-1) ha
  simp at h
  -- h : TendsTo (fun n => -a n) (-t)
  exact h

-- Proof 2
-- =======

theorem tendsTo_neg'
  (ha : TendsTo a t)
  : TendsTo (fun n ↦ -a n) (-t) :=
by
  simpa using tendsTo_const_mul (-1) ha

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that if `a(n) - b(n)` tends to `t` and `b(n)` tends
-- to `u` then `a(n)` tends to `t + u`.
-- ---------------------------------------------------------------------

-- Proof 1
-- =======

example
  (h1 : TendsTo (fun n ↦ a n - b n) t)
  (h2 : TendsTo b u) : TendsTo a (t + u) :=
by
  rw [TendsTo] at *
  intro ε hε
  have hε' : 0 < ε / 2 := by linarith
  obtain ⟨B1, hB1⟩ := h1 (ε / 2) hε'
  obtain ⟨B2, hB2⟩ := h2 (ε / 2) hε'
  use max B1 B2
  intro n hn
  have ⟨hnB1, hnB2⟩ : (n ≥ B1) ∧ (n ≥ B2) := by exact ⟨le_of_max_le_left hn, le_of_max_le_right hn⟩
  specialize hB1 n hnB1
  specialize hB2 n hnB2
  calc
    |a n - (t + u)| = |a n - b n + (b n - (t + u))| := by rw [← sub_add_sub_cancel]
    _ = |(a n - b n) + (b n - (t + u))| := by rw [sub_add_eq_sub_sub, sub_eq_add_neg]
    _ = |(a n - b n) + (- t + (b n - u))| := by
      have h : b n - (t + u) = - t + (b n - u) := by ring
      rw [h]
    _ = |(a n - b n - t) + (b n - u)| := by
      have h : (a n - b n) + (- t + (b n - u)) = (a n - b n - t) + (b n - u) := by ring
      rw [h]
    _ ≤ |a n - b n - t| + |b n - u| := by exact abs_add _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by linarith

-- Comentario de JA: La 1ª demostración no usa los ejercicios anteriores
-- y se debe de eliminar.

-- Proof 2
-- =======

example
  (h1 : TendsTo (fun n ↦ a n - b n) t)
  (h2 : TendsTo b u)
  : TendsTo a (t + u) :=
by
  simpa using tendsTo_add h1 h2

-- Comentario de JA: La 2ª demostración se puede detallar como se
-- muestra a continuación.

-- Proof 3
-- =======

theorem tendsTo_of_tendsTo_sub
  (h1 : TendsTo (fun n ↦ a n - b n) t)
  (h2 : TendsTo b u)
  : TendsTo a (t + u) :=
by
  have h3 : TendsTo (fun n ↦ (a n - b n) + (b n)) (t + u)
    := tendsTo_add h1 h2
  simp at h3
  -- h3 : TendsTo (fun n => a n) (t + u)
  exact h3

-- ---------------------------------------------------------------------
-- Exercise 8. Prove that `a(n)` tends to `t` iff `a(n)-t` tends to
-- `0`.
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- The two implications will be demonstrated.
--
-- (⟹) Suppose that
--    a(n) tends to t                                              (1)
-- Also, by tendsTo_const,
--    (n ↦ t) tends to t                                           (2)
-- From (1) and (2), by tendsTo_sub, it follows that
--    (n ↦ a(n) - t) tends to (t - t)
-- Simplifying, we obtain that
--    (n ↦ a(n) - t) tends to 0
--
-- (⟸) Suppose that
--    (n ↦ a(n) - t) tends to 0                                    (3)
-- From (3) and (2), by tendsTo_sub, it follows that
--    (n ↦ a(n) - t + t) tends to (0 + t)
-- Simplifying, we obtain that
--    a(n) tends to t

-- Proof 1
-- =======

example
  : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 :=
by
  constructor
  . -- ⊢ TendsTo a t → TendsTo (fun n => a n - t) 0
    intro h
    -- h : TendsTo a t
    -- ⊢ TendsTo (fun n => a n - t) 0
    rw [TendsTo] at *
    -- h : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
    -- ⊢ ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t - 0| < ε
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t - 0| < ε
    specialize h ε hε
    -- h : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
    cases' h with X hX
    -- X : ℕ
    -- hX : ∀ (n : ℕ), X ≤ n → |a n - t| < ε
    use X
    -- ⊢ ∀ (n : ℕ), X ≤ n → |a n - t - 0| < ε
    intro n hn
    -- n : ℕ
    -- hn : X ≤ n
    -- ⊢ |a n - t - 0| < ε
    specialize hX n hn
    -- hX : |a n - t| < ε
    simp
    -- ⊢ |a n - t| < ε
    exact hX
  . -- ⊢ TendsTo (fun n => a n - t) 0 → TendsTo a t
    intro h
    -- h : TendsTo (fun n => a n - t) 0
    -- ⊢ TendsTo a t
    rw [TendsTo] at *
    -- h : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t - 0| < ε
    -- ⊢ ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
    specialize h ε hε
    -- h : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t - 0| < ε
    cases' h with X hX
    -- X : ℕ
    -- hX : ∀ (n : ℕ), X ≤ n → |a n - t - 0| < ε
    use X
    -- ⊢ ∀ (n : ℕ), X ≤ n → |a n - t| < ε
    intro n hn
    -- n : ℕ
    -- hn : X ≤ n
    -- ⊢ |a n - t| < ε
    specialize hX n hn
    -- hX : |a n - t - 0| < ε
    simp at hX
    -- hX : |a n - t| < ε
    exact hX

-- Proof 2
-- =======

example
  : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 :=
by
  constructor
  · -- ⊢ TendsTo a t → TendsTo (fun n => a n - t) 0
    intro h
    -- h : TendsTo a t
    -- ⊢ TendsTo (fun n => a n - t) 0
    simpa using tendsTo_sub h (tendsTo_const t)
  · -- ⊢ TendsTo (fun n => a n - t) 0 → TendsTo a t
    intro h
    -- h : TendsTo (fun n => a n - t) 0
    -- ⊢ TendsTo a t
    simpa using tendsTo_add h (tendsTo_const t)

-- Comentario de JA: La 2ª demostración se puede desarrollar como se
-- muestra a continuación.

-- Proof 3
-- =======

theorem tendsTo_sub_lim_iff
  : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 :=
by
  constructor
  · -- ⊢ TendsTo a t → TendsTo (fun n => a n - t) 0
    intro h
    -- h : TendsTo a t
    -- ⊢ TendsTo (fun n => a n - t) 0
    have h1 : TendsTo (fun n => t) t
      := tendsTo_const t
    have h2 : TendsTo (fun n => a n - t) (t - t)
      := tendsTo_sub h h1
    have h3 : TendsTo (fun n => a n - t) 0
      := by simp_all only [sub_self]
    exact h3
  · -- ⊢ TendsTo (fun n => a n - t) 0 → TendsTo a t
    intro h
    -- h : TendsTo (fun n => a n - t) 0
    -- ⊢ TendsTo a t
    have h1 : TendsTo (fun n => t) t
      := tendsTo_const t
    have h2 : TendsTo (fun n => a n - t + t) (0 + t)
      := tendsTo_add h h1
    have h3 : TendsTo a t
      := by simp_all only [sub_add_cancel, zero_add]
    exact h3

-- ---------------------------------------------------------------------
-- Exercise 9. Prove that if `a(n)` and `b(n)` both tend to zero, then
-- their product tends to zero.
-- ---------------------------------------------------------------------

-- Natural language proof
-- ======================

-- Since a(n) and b(n) tend to 0, there exist X, Y ∈ ℕ such that
--    (∀n ∈ ℕ)[X ≤ n → |a(n) - 0| < ε]                               (1)
--    (∀n ∈ ℕ)[Y ≤ n → |b(n) - 0| < 1]                               (2)
-- Let
--    Z = máx(X, Y).                                                 (3)
-- We are going to prove that
--    (∀n ∈ ℕ)[Z ≤ n → |a(n)·b(n) - 0| < ε]
-- For this, let n ∈ ℕ such that
--    Z ≤ n                                                          (4)
-- By (3) and (4) we have that
--    X ≤ n                                                          (5)
--    Y ≤ n                                                          (6)
-- By (5) and (1), we have that
--    |a(n)| < ε                                                     (7)
-- By (6) and (2), we have that
--    |b(n)| < 1                                                     (8)
-- Therefore
--    |a(n)·b(n) - 0| = |a(n)|·|b(n)|
--                    < ε·1             [by (7) and (8)]
--                    = ε

-- Proof 1
-- =======

example
  (ha : TendsTo a 0)
  (hb : TendsTo b 0)
  : TendsTo (fun n ↦ a n * b n) 0 :=
by
  rw [TendsTo] at *
  -- ha : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - 0| < ε
  -- hb : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |b n - 0| < ε
  -- ⊢ ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n * b n - 0| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n * b n - 0| < ε
  have hsqrteps : 0 < √ε := Real.sqrt_pos_of_pos hε
  obtain ⟨X, hX⟩ := ha (√ε) hsqrteps
  -- X : ℕ
  -- hX : ∀ (n : ℕ), X ≤ n → |a n - 0| < √ε
  obtain ⟨Y, hY⟩ := hb (√ε) hsqrteps
  -- Y : ℕ
  -- hY : ∀ (n : ℕ), Y ≤ n → |b n - 0| < √ε
  use Nat.max X Y
  -- ⊢ ∀ (n : ℕ), X.max Y ≤ n → |a n * b n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : X.max Y ≤ n
  -- ⊢ |a n * b n - 0| < ε
  specialize hX n (le_of_max_le_left hn)
  -- hX : |a n - 0| < √ε
  specialize hY n (le_of_max_le_right hn)
  -- hY : |b n - 0| < √ε
  rw [sub_zero] at *
  -- hX : |a n| < √ε
  -- hY : |b n| < √ε
  -- ⊢ |a n * b n| < ε
  have han : 0 ≤ |a n| := abs_nonneg (a n)
  have hbn : 0 ≤ |b n| := abs_nonneg (b n)
  calc |a n * b n|
     = |a n| * |b n| := abs_mul (a n) (b n)
   _ < √ε * √ε       := mul_lt_mul'' hX hY han hbn
   _ = ε             := Real.mul_self_sqrt (le_of_lt hε)

-- Proof 2
-- =======

example
  (ha : TendsTo a 0)
  (hb : TendsTo b 0)
  : TendsTo (fun n ↦ a n * b n) 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n * b n) n - 0| < ε
  obtain ⟨X, hX⟩ := ha ε hε
  -- X : ℕ
  -- hX : ∀ (n : ℕ), X ≤ n → |a n - 0| < ε
  obtain ⟨Y, hY⟩ := hb 1 zero_lt_one
  -- Y : ℕ
  -- hY : ∀ (n : ℕ), Y ≤ n → |b n - 0| < 1
  use Nat.max X Y
  -- ⊢ ∀ (n : ℕ), X.max Y ≤ n → |(fun n => a n * b n) n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : X.max Y ≤ n
  -- ⊢ |(fun n => a n * b n) n - 0| < ε
  specialize hX n (le_of_max_le_left hn)
  -- hX : |a n - 0| < ε
  specialize hY n (le_of_max_le_right hn)
  -- hY : |b n - 0| < 1
  rw [sub_zero] at *
  -- hX : |a n| < ε
  -- hY : |b n| < 1
  -- ⊢ |(fun n => a n * b n) n| < ε
  simpa [abs_mul] using mul_lt_mul'' hX hY

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación .

-- Proof 3
-- =======

example
  (ha : TendsTo a 0)
  (hb : TendsTo b 0)
  : TendsTo (fun n ↦ a n * b n) 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n * b n) n - 0| < ε
  simp [sub_zero]
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n * b n| < ε
  obtain ⟨X, hX⟩ := ha ε hε
  -- X : ℕ
  -- hX : ∀ (n : ℕ), X ≤ n → |a n - 0| < ε
  have h1 : 0 < (1 : ℝ) := Real.zero_lt_one
  obtain ⟨Y, hY⟩ := hb 1 h1
  -- Y : ℕ
  -- hY : ∀ (n : ℕ), Y ≤ n → |b n - 0| < 1
  let Z := Nat.max X Y
  use Z
  -- ⊢ ∀ (n : ℕ), Z ≤ n → |a n * b n| < ε
  intro n hn
  -- n : ℕ
  -- hn : Z ≤ n
  -- ⊢ |a n * b n | < ε
  have hX : |a n - 0| < ε := hX n (le_of_max_le_left hn)
  have hY : |b n - 0| < 1 := hY n (le_of_max_le_right hn)
  rw [sub_zero] at *
  -- hX : |a n| < ε
  -- hY : |b n| < 1
  have han : 0 ≤ |a n| := abs_nonneg (a n)
  have hbn : 0 ≤ |b n| := abs_nonneg (b n)
  calc |a n * b n|
     = |a n| * |b n| := abs_mul (a n) (b n)
   _ < ε * 1         := mul_lt_mul'' hX hY han hbn
   _ = ε             := mul_one ε

-- Comentario de JA: La 2ª demostración se puede desarrollar como se
-- muestra a continuación.

-- Proof 4
-- =======

theorem tendsTo_zero_mul_tendsTo_zero
  (ha : TendsTo a 0)
  (hb : TendsTo b 0)
  : TendsTo (fun n ↦ a n * b n) 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n * b n) n - 0| < ε
  simp [abs_zero]
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n * b n| < ε
  obtain ⟨X, hX⟩ := ha ε hε
  -- X : ℕ
  -- hX : ∀ (n : ℕ), X ≤ n → |a n - 0| < ε
  obtain ⟨Y, hY⟩ := hb 1 zero_lt_one
  -- Y : ℕ
  -- hY : ∀ (n : ℕ), Y ≤ n → |b n - 0| < 1
  let Z := Nat.max X Y
  use Z
  -- ⊢ ∀ (n : ℕ), Z ≤ n → |a n * b n| < ε
  intro n hn
  -- n : ℕ
  -- hn : Z ≤ n
  -- ⊢ |a n * b n| < ε
  have hX : |a n - 0| < ε := hX n (le_of_max_le_left hn)
  have hY : |b n - 0| < 1 := hY n (le_of_max_le_right hn)
  simp [abs_zero] at hX hY
  -- hX : |a n| < ε
  -- hY : |b n| < 1
  have han : 0 ≤ |a n| := abs_nonneg (a n)
  have hbn : 0 ≤ |b n| := abs_nonneg (b n)
  calc |a n * b n|
     = |a n| * |b n| := abs_mul (a n) (b n)
   _ < ε * 1         := mul_lt_mul'' hX hY han hbn
   _ = ε             := mul_one ε

-- ---------------------------------------------------------------------
-- Exercise 10. Prove that if `a(n)` tends to `t` and `b(n)` tends to
-- `u` then `a(n)·b(n)` tends to `t·u`.
-- ---------------------------------------------------------------------

theorem tendsTo_mul_detailed (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
  TendsTo (fun n ↦ a n * b n) (t * u) := by
  rw [TendsTo] at *
  intro ε hε
  specialize ha ε hε
  specialize hb ε hε
  cases' ha with X hX
  cases' hb with Y hY
  use max X Y
  intro n hn
  specialize hX n (le_of_max_le_left hn)
  specialize hY n (le_of_max_le_right hn)
  sorry

/- Automatic proof -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  rw [tendsTo_sub_lim_iff] at *
  have h : ∀ n, a n * b n - t * u = (a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u := by
    intro n; ring
  simp [h]
  rw [show (0 : ℝ) = 0 + t * 0 + 0 * u by simp]
  refine' tendsTo_add (tendsTo_add _ _) _
  · exact tendsTo_zero_mul_tendsTo_zero ha hb
  · exact tendsTo_const_mul t hb
  · exact tendsTo_mul_const u ha

/- 11. tendsTo_unique -/

/- Automatic proof -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t :=
  by
  by_contra h
  wlog h2 : s < t
  · cases' Ne.lt_or_lt h with h3 h3
    · contradiction
    · apply this _ _ _ ht hs _ h3
      exact ne_comm.mp h
  set ε := t - s with hε
  have hε : 0 < ε := sub_pos.mpr h2
  obtain ⟨X, hX⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Y, hY⟩ := ht (ε / 2) (by linarith)
  specialize hX (max X Y) (le_max_left X Y)
  specialize hY (max X Y) (le_max_right X Y)
  rw [abs_lt] at hX hY
  linarith

end Section2sheet6
