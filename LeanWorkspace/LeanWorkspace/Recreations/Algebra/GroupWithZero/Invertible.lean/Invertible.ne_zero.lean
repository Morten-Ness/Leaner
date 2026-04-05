import Mathlib

open scoped Ring

variable {α : Type u}

theorem Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 := fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟a * a := by simp [ha]
      _ = 1 := invOf_mul_self

