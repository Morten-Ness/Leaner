import Mathlib

variable [MulZeroClass R] [IsCancelMulZero R] {a : R}

theorem isRegular_iff_ne_zero [Nontrivial R] : IsRegular a ↔ a ≠ 0 := ⟨IsRegular.ne_zero, .of_ne_zero⟩

