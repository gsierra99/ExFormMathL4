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
-- Exercise 3. Prove that the sequence a tends to t if and only if
--    ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε
-- ---------------------------------------------------------------------

theorem tendsTo_def
  {a : ℕ → ℝ}
  {t : ℝ}
  : TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl

theorem tendsTo_thirtyseven : TendsTo (fun _n ↦ 37) 37 := by
  rw [tendsTo_def]
  intro ε hε
  use 100
  intro n _hn
  norm_num
  exact hε

theorem tendsTo_const (c : ℝ) : TendsTo (fun _n ↦ c) c := by
  intro ε hε
  dsimp only
  use 37
  intro n _hn
  ring_nf
  norm_num
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
