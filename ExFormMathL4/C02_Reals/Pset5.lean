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

theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) :=
  by
  rw [tendsTo_def] at ha
  rw [tendsTo_def]
  intro ε hε
  specialize ha ε hε
  cases' ha with B hB
  use B
  intro n hn
  specialize hB n hn
  norm_num
  rw [abs_sub_comm] at hB
  rw [abs_lt] at hB
  rw [abs_lt]
  cases' hB with h1 h2
  constructor
  linarith
  linarith

theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) := by
  rw [tendsTo_def] at *
  intro ε hε
  specialize ha (ε / 2) (by linarith)
  cases' ha with X hX
  obtain ⟨Y, hY⟩ := hb (ε / 2) (by linarith)
  use max X Y
  intro n hn
  rw [max_le_iff] at hn
  specialize hX n hn.1
  specialize hY n hn.2
  rw [abs_lt] at *
  constructor <;>
    linarith

theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  simpa [sub_eq_add_neg] using tendsTo_add ha (tendsTo_neg hb)

end Section2sheet5
