-- C02_Reals/Pset3.lean
-- Problem set 3: Limits of sequences in Lean.
-- Gabriel Sierra Gallego.
-- Seville, October 27, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we give the standard definition of the limit of
-- a sequence and prove some theorems about the.
--
-- It is based on [Section01logic/Sheet4.lean](https://tinyurl.com/25sc8h3b)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

namespace Section2sheet3

-- ---------------------------------------------------------------------
-- Exercise 1. Define the function
--    f : ℕ → ℝ
-- such that f(n) is n² + 3.
-- ---------------------------------------------------------------------

def f : ℕ → ℝ := fun n ↦ n ^ 2 + 3

-- ---------------------------------------------------------------------
-- Exercise 2. Define the function
--    TendsTo : (ℕ → ℝ) → ℝ → Prop
-- such that (TendsTo a t) means that the sequence a tends to t; that
-- is, the limit of a(n) as n tends to infinity is t.
-- ---------------------------------------------------------------------

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that t is the limit of the sequence a if and only
-- if
--    ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε
-- ---------------------------------------------------------------------

theorem tendsTo_def
  {a : ℕ → ℝ}
  {t : ℝ}
  : TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
by
  rfl

-- ---------------------------------------------------------------------
-- Exercise 4. Prove that the limit of the constant sequence with value
-- 37 is 37.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- We need to prove that for every ε ∈ ℝ such that ε > 0, there exists an
-- N ∈ ℕ such that
--    (∀n ∈ ℕ)[n ≥ N → |37 - 37| < ε].
-- It is sufficient to take N as 1, since for all n ≥ N we have
--    |37 - 37| = |0|
--              = 0
--              < ε

-- Proofs with Lean4
-- =================

-- Proof 1
example :
  TendsTo (fun _n ↦ 37) 37 :=
by
  rw [tendsTo_def]
  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |37 - 37| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |37 - 37| < ε
  use 1
  -- ⊢ ∀ (n : ℕ), 100 ≤ n → |37 - 37| < ε
  intro n _hn
  -- n : ℕ
  -- _hn : 1 ≤ n
  -- ⊢ |37 - 37| < ε
  show |37 - 37| < ε
  calc |37 - 37| = |(0 : ℝ)| := by {congr ; exact sub_self 37}
               _ = 0         := abs_zero
               _ < ε         := hε

-- Proof 2
theorem tendsTo_thirtyseven :
  TendsTo (fun _n ↦ 37) 37 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |37 - 37| < ε
  use 100
  -- ⊢ ∀ (n : ℕ), 100 ≤ n → |37 - 37| < ε
  intro n _hn
  -- n : ℕ
  -- _hn : 100 ≤ n
  -- ⊢ |37 - 37| < ε
  norm_num
  -- ⊢ 0 < ε
  exact hε

-- ---------------------------------------------------------------------
-- Exercise 5. Prove that the limit of the constant sequence with value
-- c is c.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- We need to prove that for every ε ∈ ℝ such that ε > 0, there exists an
-- N ∈ ℕ such that
--    (∀n ∈ ℕ)[n ≥ N → |(fun _n => c) n - c| < ε].
-- It is sufficient to take N as 1, since for all n ≥ N we have
--    |(fun _n => c) n - c| = |c - c|
--                          = |0|
--                          = 0
--                          < ε

-- Proofs with Lean4
-- =================

-- Proof 1
example
  (c : ℝ)
  : TendsTo (fun _n ↦ c) c :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun _n => c) n - c| < ε
  use 1
  -- ⊢ ∀ (n : ℕ), 1 ≤ n → |(fun _n => c) n - c| < ε
  intro n _hn
  -- n : ℕ
  -- _hn : 1 ≤ n
  -- ⊢ |(fun _n => c) n - c| < ε
  show |(fun _n => c) n - c| < ε
  calc |(fun _n => c) n - c|
     = |c - c|   := by rfl
   _ = |(0 : ℝ)| := by {congr ; exact sub_self c}
   _ = 0         := abs_zero
   _ < ε         := hε

-- Proof 2
theorem tendsTo_const
  (c : ℝ)
  : TendsTo (fun _n ↦ c) c :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun _n => c) n - c| < ε
  dsimp only
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |c - c| < ε
  use 1
  -- ⊢ ∀ (n : ℕ), 1 ≤ n → |c - c| < ε
  intro n _hn
  -- n : ℕ
  -- _hn : 1 ≤ n
  -- ⊢ |c - c| < ε
  ring_nf
  -- ⊢ |0| < ε
  norm_num
  -- ⊢ 0 < ε
  exact hε

theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) := by
  rw [tendsTo_def] at h
  rw [tendsTo_def]
  intro ε hε
  specialize h ε hε
  cases' h with B hB
  use B
  intro n hn
  specialize hB n hn
  norm_num
  exact hB


example {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n => -a n) (-t) := by
  rw [tendsTo_def] at ha
  rw [tendsTo_def]
  intro ε hε
  specialize ha ε hε
  cases' ha with B hB
  use B
  intro n hn
  specialize hB n hn
  norm_num
  have : -a n + t = -(a n - t) := by ring
  rw [this, abs_neg]
  exact hB

end Section2sheet3
