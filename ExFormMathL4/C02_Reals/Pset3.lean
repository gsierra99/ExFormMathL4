-- C02_Reals/Pset3.lean
-- Problem set 3: Limits of sequences in Lean.
-- Gabriel Sierra Gallego.
-- Seville, October 27, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we give the standard definition of the limit of
-- a sequence and prove some theorems about the.
--
-- It is based on [Section02reals/Sheet3.lean](https://tinyurl.com/29tfe98x)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic

namespace Section2sheet3

variable {c : ℝ}
variable {t : ℝ}
variable {a : ℕ → ℝ}

-- ---------------------------------------------------------------------
-- Exercise 1. Define the function
--    f : ℕ → ℝ
-- such that f(n) is n² + 3.
-- ---------------------------------------------------------------------

def f : ℕ → ℝ := fun n ↦ n ^ 2 + 3

-- ---------------------------------------------------------------------
-- Exercise 2. Define the function
--    TendsTo : (ℕ → ℝ) → ℝ → Prop
-- such that `TendsTo a t` means that the sequence `a` tends to `t`; that
-- is, the limit of `a(n)` as `n` tends to infinity is `t`.
-- ---------------------------------------------------------------------

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that `t` is the limit of the sequence `a` if and
-- only if
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
-- `c` is `c`.
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

-- ---------------------------------------------------------------------
-- Exercise 6. Prove that if `a(n)` tends to `t` then `a(n) + c` tends
-- to `t + c`.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Let ε ∈ ℝ such that ε > 0. We need to prove that
--    (∃ N)(∀ n ≥ N)[|(a(n) + c) - (t + c)| < ε]                     (1)
-- Since the limit of the sequence a(i) is t, there exists a k such that
--    (∀ n ≥ k)[|a(n) - t| < ε]                                      (2)
-- Let's see that (1) holds with k; that is, that
--    (∀ n ≥ k)[|(a(n) + c) - (t + c)| < ε]
-- Let n ≥ k. Then, by (2),
--    |a(n) - t| < ε                                                 (3)
-- and, consequently,
--    |(a(n) + c) - (t + c)| = |a(n) - t|
--                           < ε            [by (3)]

-- Proofs with Lean4
-- =================

-- Proof 1
example
  (h : TendsTo a t)
  : TendsTo (fun n => a n + c) (t + c) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n + c) n - (t + c)| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + c - (t + c)| < ε
  obtain ⟨k, hk⟩ := h ε hε
  -- k : ℕ
  -- hk : ∀ (n : ℕ), k ≤ n → |a n - t| < ε
  use k
  -- ⊢ ∀ (n : ℕ), k ≤ n → |a n + c - (t + c)| < ε
  intros n hn
  -- n : ℕ
  -- hn : k ≤ n
  calc |a n + c - (t + c)|
     = |a n - t|           := by norm_num
   _ < ε                   := hk n hn

-- Proof 2
example
  (h : TendsTo a t)
  : TendsTo (fun n => a n + c) (t + c) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |(fun i => u i + c) n - (a + c)| < ε
  dsimp
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → |u n + c - (a + c)| < ε
  obtain ⟨k, hk⟩ := h ε hε
  -- k : ℕ
  -- hk : ∀ (n : ℕ), n ≥ k → |u n - a| < ε
  use k
  -- ⊢ ∀ (n : ℕ), n ≥ k → |u n + c - (a + c)| < ε
  intros n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |u n + c - (a + c)| < ε
  convert hk n hn using 2
  -- ⊢ u n + c - (a + c) = u n - a
  ring

-- Proof 3
theorem tendsTo_add_const
  (h : TendsTo a t)
  : TendsTo (fun n => a n + c) (t + c) :=
by
  rw [tendsTo_def] at h
  -- h : ∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  rw [tendsTo_def]
  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |a n + c - (t + c)| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + c - (t + c)| < ε
  specialize h ε hε
  -- h : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  cases' h with B hB
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |a n + c - (t + c)| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |a n + c - (t + c)| < ε
  specialize hB n hn
  -- hB : |a n - t| < ε
  norm_num
  -- ⊢ |a n - t| < ε
  exact hB

-- ---------------------------------------------------------------------
-- Exercise 7. Prove that if `a(n)` tends to `t` then `-a(n)` tends to
-- `-t`.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- Let ε ∈ ℝ such that ε > 0. We need to prove that
--    (∃ N ∈ ℕ)(∀ n ≥ N)[|-aₙ - -t| < ε]                             (1)
-- Since the limit of aₙ is t, there exists a k ∈ ℕ such that
--    (∀ n ≥ k)[|aₙ - t| < ε]                                        (2)
-- Let's see that (1) holds with k. Indeed, let n ≥ k. Then,
--    |-aₙ - -t| = |-(aₙ - t)|
--               = |aₙ - t|
--               < ε           [by (2)]

-- Proofs with Lean4
-- =================

-- Proof 1
example
  (ha : TendsTo a t)
  : TendsTo (fun n => -a n) (-t) :=
by
  rw [tendsTo_def] at ha
  -- ha : ∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  rw [tendsTo_def]
  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |-a n - -t| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |-a n - -t| < ε
  specialize ha ε hε
  -- ha : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  cases' ha with B hB
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |-a n - -t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |-a n - -t| < ε
  specialize hB n hn
  -- hB : |a n - t| < ε
  norm_num
  -- ⊢ |-a n + t| < ε
  have : -a n + t = -(a n - t) := by ring
  rw [this, abs_neg]
  -- ⊢ |a n - t| < ε
  exact hB

-- Comentario de JA: La 1ª demostración se puede simplificar como se
-- muestra a continuación.

-- Proof 2
example
  (ha : TendsTo a t)
  : TendsTo (fun n => -a n) (-t) :=
by
  unfold TendsTo at *
  -- ha : ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  -- ⊢ ∀ ε > 0, ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => -a n) n - -t| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => -a n) n - -t| < ε
  specialize ha ε hε
  -- ha : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  obtain ⟨B, hB⟩ := ha
  -- B : ℕ
  -- hB : ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  use B
  -- ⊢ ∀ (n : ℕ), B ≤ n → |(fun n => -a n) n - -t| < ε
  intro n hn
  -- n : ℕ
  -- hn : B ≤ n
  -- ⊢ |(fun n => -a n) n - -t| < ε
  calc |(fun n => -a n) n - -t|
       = |-a n - -t|          := rfl
     _ = |-(a n - t)|         := by congr ; ring
     _ = |a n - t|            := abs_neg (a n - t)
     _ < ε                    := hB n hn


end Section2sheet3
