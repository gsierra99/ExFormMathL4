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
variable {t : ℝ }

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

/- 3. tendsTo_neg_const_mul -/

/- Detailed proof -/
theorem tendsTo_neg_const_mul_detailed {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
  TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [TendsTo] at *
  intro ε hε
  have hc' : 0 < -c := by linarith
  have heps : 0 < ε / -c := by exact div_pos hε hc'
  obtain ⟨X, hX⟩ := h (ε / -c) heps
  use X
  intro n hn
  specialize hX n hn
  calc
    |c * a n - c * t| = |c * (a n - t)| := by rw [← mul_sub]
    _ = |c| * |a n - t| := by rw [abs_mul]
    _ = -c * |a n - t| := by rw [abs_of_nonpos]; linarith
    _ < -c * (ε / -c) := by exact (mul_lt_mul_left hc').mpr hX
    _ = (-c * ε) / -c := by exact Eq.symm (mul_div_assoc (-c) ε (-c))
    _ = (ε * -c) / -c := by rw [mul_comm]
    _ = ε * (-c / -c) := by rw [mul_div_assoc ε (-c) (-c)]
    _ = ε * (c / c) := by rw [neg_div_neg_eq]
    _ = ε * 1 := by
      have hc'' : c ≠ 0 := by linarith
      rw [div_self hc'']
    _ = ε := by linarith

/- Automatic proof -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) :=
  by
  have hc' : 0 < -c := neg_pos.mpr hc
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / -c) (div_pos hε hc')
  use X
  intro n hn
  specialize hX n hn
  simp
  rw [← mul_sub, abs_mul, abs_of_neg hc]
  exact (lt_div_iff₀' hc').mp hX

/- 4. tendsTo_const_mul -/

/- Detailed proof -/
theorem tendsTo_const_mul_detailed {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
  TendsTo (fun n ↦ c * a n) (c * t) := by
  obtain hcpos | hczero | hcneg := lt_trichotomy 0 c
  exact tendsTo_pos_const_mul h hcpos
  rw [← hczero]
  simp
  exact tendsTo_const 0
  exact tendsTo_neg_const_mul h hcneg

/- Automatic proof -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) :=
  by
  obtain hc | rfl | hc := lt_trichotomy 0 c
  · exact tendsTo_pos_const_mul h hc
  · simpa using tendsTo_const 0
  · exact tendsTo_neg_const_mul h hc

/- 5. tendsTo_mul_const -/

/- Detailed proof -/
theorem tendsTo_mul_const_detailed {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
  TendsTo (fun n ↦ a n * c) (t * c) := by
  simp [mul_comm]
  rw [mul_comm]
  exact tendsTo_const_mul c h

/- Automatic proof -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by

  simpa [mul_comm] using tendsTo_const_mul c h

/- 6. tendsTo_neg' -/

/- Detailed proof -/
theorem tendsTo_neg'_detailed {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  have h : TendsTo (fun n ↦ -1 * a n) (-1 * t) := tendsTo_const_mul (-1) ha
  simp at h
  exact h


/- Automatic proof -/
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/- 6. tendsTo_of_tendsTo_sub -/

/- Detailed proof -/
theorem tendsTo_of_tendsTo_sub_detailed {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
  (h2 : TendsTo b u) : TendsTo a (t + u) := by
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


/- Automatic proof -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by

  simpa using tendsTo_add h1 h2

/- 7. tendsTo_sub_lim_iff -/

/- Detailed proof -/
theorem tendsTo_sub_lim_iff_detailed {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  intro h
  rw [TendsTo] at *
  intro ε hε
  specialize h ε hε
  cases' h with X hX
  use X
  intro n hn
  specialize hX n hn
  simp
  exact hX
  intro h
  rw [TendsTo] at *
  intro ε hε
  specialize h ε hε
  cases' h with X hX
  use X
  intro n hn
  specialize hX n hn
  simp at hX
  exact hX

/- Automatic proof -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 :=
  by
  constructor
  · intro h
    simpa using tendsTo_sub h (tendsTo_const t)
  · intro h
    simpa using tendsTo_add h (tendsTo_const t)

/- 8. tendsTo_zero_mul_tendsTo_zero -/

/- Detailed proof -/
theorem tendsTo_zero_mul_tendsTo_zero_detailed {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
  TendsTo (fun n ↦ a n * b n) 0 := by
  rw [TendsTo] at *
  intro ε hε
  have hsqrteps : 0 < ε^(1/2) := by exact pow_pos hε (1 / 2)
  obtain ⟨X, hX⟩ := ha (ε^(1/2)) hsqrteps
  obtain ⟨Y, hY⟩ := hb (ε^(1/2)) hsqrteps
  use max X Y
  intro n hn
  specialize hX n (le_of_max_le_left hn)
  specialize hY n (le_of_max_le_right hn)
  rw [sub_zero] at *
  calc
    |a n * b n| = |a n| * |b n| := by rw [abs_mul]
    _ < ε^(1/2) * ε^(1/2) := sorry
    _ = ε := sorry

/- Automatic proof -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  intro ε hε
  obtain ⟨X, hX⟩ := ha ε hε
  obtain ⟨Y, hY⟩ := hb 1 zero_lt_one
  use max X Y
  intro n hn
  specialize hX n (le_of_max_le_left hn)
  specialize hY n (le_of_max_le_right hn)
  simpa [abs_mul] using mul_lt_mul'' hX hY

/- 9. tendsTo_mul -/

/- Detailed proof -/
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

/- 10. tendsTo_unique -/

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
