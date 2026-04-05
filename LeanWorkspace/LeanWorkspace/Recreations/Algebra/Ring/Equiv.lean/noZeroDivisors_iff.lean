import Mathlib

variable {F α β R S S' : Type*}

variable {A B : Type*} [MulZeroClass A] [MulZeroClass B]

theorem noZeroDivisors_iff (e : A ≃* B) : NoZeroDivisors A ↔ NoZeroDivisors B where
  mp _ := MulEquiv.noZeroDivisors e.symm
  mpr _ := MulEquiv.noZeroDivisors e

