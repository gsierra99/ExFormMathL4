import Mathlib.Tactic
import ExFormMathL4.S02_Reals.Pset3

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
  sorry

end Section2sheet5
