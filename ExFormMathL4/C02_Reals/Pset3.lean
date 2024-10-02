import Mathlib.Tactic

namespace Section2sheet3

def f : ℕ → ℝ := fun n ↦ n ^ 2 + 3
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl

theorem tendsTo_thirtyseven : TendsTo (fun _n ↦ 37) 37 :=
  by
  rw [tendsTo_def]
  intro ε hε
  use 100
  intro n _hn
  norm_num
  exact hε

theorem tendsTo_const (c : ℝ) : TendsTo (fun _n ↦ c) c :=
  by
  intro ε hε
  dsimp only
  use 37
  intro n _hn
  ring_nf
  norm_num
  exact hε

theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) :=
  by
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
  sorry

end Section2sheet3
