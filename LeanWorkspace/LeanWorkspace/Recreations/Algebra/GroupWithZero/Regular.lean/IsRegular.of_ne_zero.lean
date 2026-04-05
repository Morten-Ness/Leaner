import Mathlib

variable [MulZeroClass R] [IsCancelMulZero R] {a : R}

theorem IsRegular.of_ne_zero (a0 : a ≠ 0) : IsRegular a := ⟨fun _ _ => mul_left_cancel₀ a0, fun _ _ => mul_right_cancel₀ a0⟩

