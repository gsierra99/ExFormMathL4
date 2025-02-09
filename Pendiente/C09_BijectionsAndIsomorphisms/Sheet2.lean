import Mathlib.Tactic

namespace Section9Sheet2


def bijection1 : ℚ ≃ ℚ where
  toFun := id
  invFun := id
  left_inv :=
    by
    intro q
    rfl
  right_inv q := rfl


def bijection2 : ℚ ≃ ℚ where
  toFun q := 3 * q + 4
  invFun r := (r - 4) / 3
  left_inv := by
    intro r
    dsimp
    ring
  right_inv := by
    intro r
    dsimp
    ring


example : bijection1 ≠ bijection2 := by
  unfold bijection1 bijection2
  intro h
  simp at h
  cases' h with h1 _
  rw [funext_iff] at h1
  specialize h1 37
  norm_num at h1
