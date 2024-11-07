-- C02_Reals/Pset5.lean
-- Problem set 5: Limits of sequences and linarith.
-- Gabriel Sierra Gallego.
-- Seville, October 28, 2024
-- ---------------------------------------------------------------------

-- In this problem set, we give the standard definition of the limit of
-- a sequence and prove some theorems about the using linarith.
--
-- It is based on [Section02reals/Sheet3.lean](https://tinyurl.com/2ym6uu4n)
-- from [Kevin Buzzard's course](https://tinyurl.com/26ek593r).

import Mathlib.Tactic
import ExFormMathL4.C02_Reals.Pset3

namespace Section2sheet5

open Section2sheet3

variable {a b : ℕ → ℝ}
variable {t u : ℝ}

-- ---------------------------------------------------------------------
-- Exercise 1. Prove that if `a(n)` tends to `t` then `-a(n)` tends to
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
-- -------

example
  (ha : TendsTo a t)
  : TendsTo (fun n ↦ -a n) (-t) :=
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
  rw [abs_sub_comm] at hB
  -- hB : |t - a n| < ε
  rw [abs_lt] at hB
  -- hB : -ε < t - a n ∧ t - a n < ε
  rw [abs_lt]
  -- ⊢ -ε < -a n + t ∧ -a n + t < ε
  cases' hB with h1 h2
  -- h1 : -ε < t - a n
  -- h2 : t - a n < ε
  constructor
  . -- ⊢ -ε < -a n + t
    linarith
  . -- ⊢ -a n + t < ε
    linarith

-- Proof 2
-- -------

theorem tendsTo_neg
  (ha : TendsTo a t)
  : TendsTo (fun n => -a n) (-t) :=
by
  have h1 : ∀ n, |a n - t| = |(-a n - -t)| := by
    intro n
    -- n : ℕ
    -- ⊢ |a n - t| = |-a n - -t|
    rw [abs_sub_comm]
    -- ⊢ |t - a n| = |-a n - -t|
    congr 1
    -- ⊢ t - a n = -a n - -t
    ring
  simpa [h1, tendsTo_def] using ha

-- ---------------------------------------------------------------------
-- Exercise 2. Prove that if `a(n)` tends to `t` and `b(n)` tends to `u`
-- then `a(n) + b(n)` tends to `t + u`.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- In the proof, we will use the following lemmas
--    (∀ a ∈ ℝ)[a > 0 → a / 2 > 0]                                   (L1)
--    (∀ a, b, c ∈ ℝ)[max(a, b) ≤ c → a ≤ c]                         (L2)
--    (∀ a, b, c ∈ ℝ)[max(a, b) ≤ c → b ≤ c]                         (L3)
--    (∀ a, b ∈ ℝ)[|a + b| ≤ |a| + |b|]                              (L4)
--    (∀ a ∈ ℝ)[a / 2 + a / 2 = a]                                   (L5)
--
-- We need to prove that for every ε ∈ ℝ, if
--    ε > 0                                                          (1)
-- then
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |(a + b)(n) - (t + u)| < ε]           (2)
--
-- From (1) and lemma L1, we have that
--    ε/2 > 0                                                        (3)
-- From (3) and because the limit of a is t, we have that
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |a(n) - t| < ε/2]
-- Let N₁ ∈ ℕ such that
--    (∀n ∈ ℕ)[n ≥ N₁ → |a(n) - t| < ε/2]                            (4)
-- From (3) and because the limit of b is u, we have that
--    (∃N ∈ ℕ)(∀n ∈ ℕ)[n ≥ N → |b(n) - u| < ε/2]
-- Let N₂ ∈ ℕ such that
--    (∀n ∈ ℕ)[n ≥ N₂ → |b(n) - u| < ε/2]                            (5)
-- Let N = max(N₁, N₂). Let's see that it satisfies condition (1). To do
-- this, let n ∈ ℕ such that n ≥ N. Then, n ≥ N₁ (by L2) and n ≥ N₂ (by
-- L3). Therefore, by properties (4) and (5), we have that
--    |a(n) - t| < ε/2                                               (6)
--    |b(n) - u| < ε/2                                               (7)
-- Finally,
--    |(a + b)(n) - (t + u)| = |(a(n) + b(n)) - (t + u)|
--                           = |(a(n) - t) + (b(n) - u)|
--                           ≤ |a(n) - t| + |b(n) - u|      [by L4]
--                           < ε/2 + ε/2                    [by (6) and (7)]
--                           = ε                            [by L5]

-- Proofs with Lean4
-- =================

-- Proof 1
-- -------

example
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n + b n) (t + u) :=
by
  rw [tendsTo_def] at *
  -- ha : ∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε
  -- hb : ∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |b n - u| < ε
  -- ⊢ ∀ (ε : ℝ), 0 < ε → ∃ B, ∀ (n : ℕ), B ≤ n → |a n + b n - (t + u)| < ε
  intro ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + b n - (t + u)| < ε
  specialize ha (ε / 2) (by linarith)
  -- ha : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < ε / 2
  cases' ha with X hX
  -- X : ℕ
  -- hX : ∀ (n : ℕ), X ≤ n → |a n - t| < ε / 2
  obtain ⟨Y, hY⟩ := hb (ε / 2) (by linarith)
  -- Y : ℕ
  -- hY : ∀ (n : ℕ), Y ≤ n → |b n - u| < ε / 2
  use max X Y
  -- ⊢ ∀ (n : ℕ), max X Y ≤ n → |a n + b n - (t + u)| < ε
  intro n hn
  -- n : ℕ
  -- hn : max X Y ≤ n
  -- ⊢ |a n + b n - (t + u)| < ε
  rw [max_le_iff] at hn
  -- hn : X ≤ n ∧ Y ≤ n
  specialize hX n hn.1
  -- hX : |a n - t| < ε / 2
  specialize hY n hn.2
  -- hY : |b n - u| < ε / 2
  rw [abs_lt] at *
  -- hX : -(ε / 2) < a n - t ∧ a n - t < ε / 2
  -- hY : -(ε / 2) < b n - u ∧ b n - u < ε / 2
  -- ⊢ -ε < a n + b n - (t + u) ∧ a n + b n - (t + u) < ε
  constructor <;> linarith

-- Proof 2
-- -------

example
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n + b n) (t + u) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n + b n) n - (t + u)| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + b n - (t + u)| < ε
  have hε2 : 0 < ε / 2 := half_pos hε
  cases' ha (ε / 2) hε2 with Nu hNu
  -- Nu : ℕ
  -- hNu : ∀ (n : ℕ), Nu ≤ n → |a n - t| < ε / 2
  cases' hb (ε / 2) hε2 with Nv hNv
  -- Nv : ℕ
  -- hNv : ∀ (n : ℕ), Nv ≤ n → |b n - u| < ε / 2
  clear ha hb hε2 hε
  let N := max Nu Nv
  use N
  -- ⊢ ∀ (n : ℕ), N ≤ n → |a n + b n - (t + u)| < ε
  intros n hn
  -- n : ℕ
  -- hn : N ≤ n
  -- ⊢ |a n + b n - (t + u)| < ε
  have nNu : n ≥ Nu := le_of_max_le_left hn
  specialize hNu n nNu
  -- hNu : |a n - t| < ε / 2
  have nNv : n ≥ Nv := le_of_max_le_right hn
  specialize hNv n nNv
  -- hNv : |b n - u| < ε / 2
  clear hn nNu nNv
  calc |(a + b) n - (t + u)|
       = |(a n + b n) - (t + u)|  := rfl
     _ = |(a n - t) + (b n - u)|  := by { congr; ring }
     _ ≤ |a n - t| + |b n - u|    := by apply abs_add
     _ < ε / 2 + ε / 2            := by linarith [hNu, hNv]
     _ = ε                        := by apply add_halves

-- Proof 3
-- -------

example
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n + b n) (t + u) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n + b n) n - (t + u)| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + b n - (t + u)| < ε
  cases' ha (ε/2) (by linarith) with Nu hNu
  -- Nu : ℕ
  -- hNu : ∀ (n : ℕ), Nu ≤ n → |a n - t| < ε / 2
  cases' hb (ε/2) (by linarith) with Nv hNv
  -- Nv : ℕ
  -- hNv : ∀ (n : ℕ), Nv ≤ n → |b n - u| < ε / 2
  use max Nu Nv
  -- ⊢ ∀ (n : ℕ), max Nu Nv ≤ n → |a n + b n - (t + u)| < ε
  intros n hn
  -- n : ℕ
  -- hn : max Nu Nv ≤ n
  -- ⊢ |a n + b n - (t + u)| < ε
  have hn₁ : n ≥ Nu := le_of_max_le_left hn
  specialize hNu n hn₁
  -- hNu : |a n - t| < ε / 2
  have hn₂ : n ≥ Nv := le_of_max_le_right hn
  specialize hNv n hn₂
  -- hNv : |b n - u| < ε / 2
  calc |(a + b) n - (t + u)|
       = |(a n + b n) - (t + u)|  := by rfl
     _ = |(a n - t) + (b n -  u)| := by {congr; ring}
     _ ≤ |a n - t| + |b n -  u|   := by apply abs_add
     _ < ε / 2 + ε / 2            := by linarith
     _ = ε                        := by apply add_halves

-- Proof 4
-- -------

lemma max_ge_iff
  {α : Type _}
  [LinearOrder α]
  {p q r : α}
  : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q :=
max_le_iff

example
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n + b n) (t + u) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n + b n) n - (t + u)| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + b n - (t + u)| < ε
  cases' ha (ε/2) (by linarith) with Nu hNu
  -- Nu : ℕ
  -- hNu : ∀ (n : ℕ), Nu ≤ n → |a n - t| < ε / 2
  cases' hb (ε/2) (by linarith) with Nv hNv
  -- Nv : ℕ
  -- hNv : ∀ (n : ℕ), Nv ≤ n → |b n - u| < ε / 2
  use max Nu Nv
  -- ⊢ ∀ (n : ℕ), max Nu Nv ≤ n → |a n + b n - (t + u)| < ε
  intros n hn
  -- n : ℕ
  -- hn : max Nu Nv ≤ n
  -- ⊢ |a n + b n - (t + u)| < ε
  cases' max_ge_iff.mp hn with hn₁ hn₂
  -- hn₁ : n ≥ Nu
  -- hn₂ : n ≥ Nv
  have cota₁ : |a n - t| < ε/2 := hNu n hn₁
  have cota₂ : |b n - u| < ε/2 := hNv n hn₂
  calc |(a + b) n - (t + u)|
       = |(a n + b n) - (t + u)| := by rfl
     _ = |(a n - t) + (b n - u)| := by { congr; ring }
     _ ≤ |a n - t| + |b n - u|   := by apply abs_add
     _ < ε                       := by linarith

-- Proof 5
-- -------

example
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n + b n) (t + u) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n + b n) n - (t + u)| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + b n - (t + u)| < ε
  cases' ha (ε/2) (by linarith) with Nu hNu
  -- Nu : ℕ
  -- hNu : ∀ (n : ℕ), Nu ≤ n → |a n - t| < ε / 2
  cases' hb (ε/2) (by linarith) with Nv hNv
  -- Nv : ℕ
  -- hNv : ∀ (n : ℕ), Nv ≤ n → |b n - u| < ε / 2
  use max Nu Nv
  -- ⊢ ∀ (n : ℕ), max Nu Nv ≤ n → |a n + b n - (t + u)| < ε
  intros n hn
  -- n : ℕ
  -- hn : max Nu Nv ≤ n
  -- ⊢ |a n + b n - (t + u)| < ε
  cases' max_ge_iff.mp hn with hn₁ hn₂
  -- hn₁ : n ≥ Nu
  -- hn₂ : n ≥ Nv
  calc |(a + b) n - (t + u)|
       = |a n + b n - (t + u)|   := by rfl
     _ = |(a n - t) + (b n - u)| := by { congr; ring }
     _ ≤ |a n - t| + |b n - u|   := by apply abs_add
     _ < ε/2 + ε/2               := add_lt_add (hNu n hn₁) (hNv n hn₂)
     _ = ε                       := by simp

-- Proof 6
-- -------

example
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n + b n) (t + u) :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n + b n) n - (t + u)| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + b n - (t + u)| < ε
  cases' ha (ε/2) (by linarith) with Nu hNu
  -- Nu : ℕ
  -- hNu : ∀ (n : ℕ), Nu ≤ n → |a n - t| < ε / 2
  cases' hb (ε/2) (by linarith) with Nv hNv
  -- Nv : ℕ
  -- hNv : ∀ (n : ℕ), Nv ≤ n → |b n - u| < ε / 2
  use max Nu Nv
  -- ⊢ ∀ (n : ℕ), max Nu Nv ≤ n → |a n + b n - (t + u)| < ε
  intros n hn
  -- n : ℕ
  -- hn : max Nu Nv ≤ n
  -- ⊢ |a n + b n - (t + u)| < ε
  rw [Nat.max_le] at hn
  calc |(a + b) n - (t + u)|
       = |a n + b n - (t + u)|   := by rfl
     _ = |(a n - t) + (b n - u)| := by { congr; ring }
     _ ≤ |a n - t| + |b n - u|   := by apply abs_add
     _ < ε                       := by linarith [hNu n (by linarith), hNv n (by linarith)]

-- Proof 7
-- -------

theorem tendsTo_add
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n + b n) (t + u) :=
by
  intros ε Hε
  -- ε : ℝ
  -- Hε : ε > 0
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |(fun n => a n + b n) n - (t + u)| < ε
  dsimp
  -- ⊢ ∃ B, ∀ (n : ℕ), B ≤ n → |a n + b n - (t + u)| < ε
  cases' ha (ε/2) (by linarith) with L HL
  -- L : ℕ
  -- HL : ∀ (n : ℕ), L ≤ n → |a n - t| < ε / 2
  cases' hb (ε/2) (by linarith) with M HM
  -- M : ℕ
  -- HM : ∀ (n : ℕ), M ≤ n → |b n - u| < ε / 2
  set N := max L M with _hN
  -- _hN : N = max L M
  use N
  -- ⊢ ∀ (n : ℕ), N ≤ n → |a n + b n - (t + u)| < ε
  have HLN : N ≥ L := le_max_left _ _
  have HMN : N ≥ M := le_max_right _ _
  intros n Hn
  -- n : ℕ
  -- Hn : N ≤ n
  -- ⊢ |a n + b n - (t + u)| < ε
  have H3 : |a n - t| < ε/2 := HL n (by linarith)
  have H4 : |b n - u| < ε/2 := HM n (by linarith)
  calc |(a + b) n - (t + u)|
       = |(a n + b n) - (t + u)|   := by rfl
     _ = |(a n - t) + (b n - u)|   := by {congr; ring }
     _ ≤ |a n - t| + |b n - u|     := by apply abs_add
     _ < ε/2 + ε/2                 := by linarith
     _ = ε                         := by ring

-- ---------------------------------------------------------------------
-- Exercise 3. Prove that if `a(n)` tends to `t` and `b(n)` tends to `u`
-- then `a(n) - b(n)` tends to `t - u`.
-- ---------------------------------------------------------------------

-- Proof in natural language
-- =========================

-- By exercise 1, -b(n) tends to -u. Moreover,
--    a(n) - b(n) = a(n) + (-b(n))
-- Then, by exercise 2, a(n) - b(n) tends to t + (-u); that is, to
-- t - u.

-- Proofs with Lean4
-- =================

-- Proof 1
-- -------

example
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n - b n) (t - u) :=
by
  simpa [sub_eq_add_neg] using tendsTo_add ha (tendsTo_neg hb)

-- Proof 2
-- -------

theorem tendsTo_sub
  (ha : TendsTo a t)
  (hb : TendsTo b u)
  : TendsTo (fun n ↦ a n - b n) (t - u) :=
by
  have h1 : TendsTo (fun n ↦ - b n) (-u) := tendsTo_neg hb
  show TendsTo (fun n ↦ a n - b n) (t - u)
  exact tendsTo_add ha h1

end Section2sheet5
