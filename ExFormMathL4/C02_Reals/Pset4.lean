import Mathlib.Tactic
example (x : ℝ) : |-x| = |x| := by
  exact abs_neg x

example (x y : ℝ) : |x - y| = |y - x| := by
  exact abs_sub_comm x y

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C := by
  exact Nat.max_le

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by
  exact abs_lt

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 := by
  exact half_pos hε

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y := by
  exact add_lt_add h1 h2

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 := by
  linarith

example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) : a + b + c + d < x + y := by
  linarith
